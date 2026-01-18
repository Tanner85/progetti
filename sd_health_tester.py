#!/usr/bin/env python3
"""
SafeSDTester - SD Card Health Testing Tool
Test SD card integrity and predict failure without losing data

Version: 2.3 (Laboratory Edition)

CHANGELOG v2.3:
- FIX: Pre-flight disk space check before backup
- FIX: Atomic backup write (temp file + rename)
- FIX: Correct offset tracking (was buggy with skipped sectors)
- FIX: Cleanup incomplete files on error/interrupt
- FIX: Graceful Ctrl+C handling with cleanup
- FIX: Report save errors don't block restore

IMPORTANT NOTES:
- This tool tests LOGICAL sectors (LBA), not physical NAND cells
- The SD controller's FTL may remap sectors transparently
- Bit error measurements are POST-ECC (controller-corrected)
- Health score is HEURISTIC, not a scientific metric

FEATURES:
- Non-destructive: automatic backup/restore
- Pattern inversion stress test (P → ~P → P)
- Walking bit patterns for directional bit detection
- Reproducible tests with seed
- Aggressive restore with retry and recovery script
- Complete per-sector metadata for forensic analysis
"""

import os
import sys
import time
import hashlib
import json
import random
import statistics
import shutil
import signal
from pathlib import Path
from datetime import datetime
from typing import List, Dict, Tuple, Optional
import argparse

# Configurazione
SECTOR_SIZE = 512  # Standard sector size
BACKUP_DIR = "/tmp/sd_tester_backup"
RESTORE_MAX_RETRIES = 5
RESTORE_RETRY_DELAY = 0.5
PROGRESS_BAR_WIDTH = 20

# Test profiles
PROFILES = {
    'quick': {
        'sectors': 1000,
        'inversion_pct': 0,      # No inversion in quick mode
        'walking_pct': 0,        # No walking in quick mode
        'description': 'Fast test (~5 min), basic health check'
    },
    'standard': {
        'sectors': 10000,
        'inversion_pct': 5,      # 5% of sectors get inversion test
        'walking_pct': 2,        # 2% of sectors get walking test
        'description': 'Balanced test (~30 min), good coverage'
    },
    'deep': {
        'sectors': 25000,
        'inversion_pct': 10,     # 10% inversion
        'walking_pct': 5,        # 5% walking
        'description': 'Thorough test (~2 hours), comprehensive analysis'
    },
    'forensic': {
        'sectors': 50000,
        'inversion_pct': 15,     # 15% inversion
        'walking_pct': 10,       # 10% walking
        'description': 'Laboratory test (~4+ hours), maximum coverage'
    }
}

# Pattern types
PATTERN_TYPES = {
    'zeros': b'\x00' * SECTOR_SIZE,
    'ones': b'\xFF' * SECTOR_SIZE,
    'alt_aa': b'\xAA' * SECTOR_SIZE,
    'alt_55': b'\x55' * SECTOR_SIZE,
}


class SafeSDTester:
    """Main class for safe SD card testing with backup/restore"""
    
    def __init__(self, device_path: str, backup_dir: str = BACKUP_DIR, 
                 seed: int = None, simulate: bool = False):
        self.device_path = device_path
        self.backup_dir = Path(backup_dir)
        self.simulate = simulate
        
        if not simulate:
            self.backup_dir.mkdir(parents=True, exist_ok=True)
        
        self.device_size = 0
        self.sector_count = 0
        self.test_sectors = []
        self.backup_data = {}
        
        # Timestamp unico per tutta la sessione
        self.session_timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        
        # Seed per riproducibilità
        self.seed = seed if seed is not None else random.randint(0, 2**32 - 1)
        
        # Device identity
        self.device_id = None
        
        # Per-sector test metadata (forensic)
        self.sector_metadata = {}
        
        # Backup file paths (per cleanup)
        self._backup_file_tmp = None
        self._backup_file = None
        self._metadata_file = None
        
        # Signal handler per interruzioni
        self._original_sigint = signal.getsignal(signal.SIGINT)
        self._interrupted = False
        
        self.results = {
            'start_time': None,
            'end_time': None,
            'device': device_path,
            'total_sectors': 0,
            'tested_sectors': 0,
            'errors': [],
            'performance': {},
            'health_score': 0,
            'seed': self.seed,
            'simulate': simulate
        }
    
    @staticmethod
    def check_permissions(device_path: str) -> Tuple[bool, str]:
        """Check if we have necessary permissions"""
        if os.geteuid() == 0:
            return True, "Running as root"
        
        if os.path.exists(device_path):
            if os.access(device_path, os.R_OK | os.W_OK):
                return True, "User has direct access to device"
        
        msg = """
Accesso negato al device. Opzioni disponibili:

1. CONSIGLIATO - Esegui con sudo:
   sudo python3 sd_health_tester.py {device}

2. ALTERNATIVA - Aggiungi utente al gruppo 'disk':
   sudo usermod -aG disk $USER
   (richiede logout/login)

3. ALTERNATIVA - Permessi temporanei:
   sudo chmod o+rw {device}
""".format(device=device_path)
        
        return False, msg
    
    def _log(self, message: str, level: str = "info"):
        """Print log message, with simulate prefix if in simulate mode"""
        prefix = "[SIMULATE] " if self.simulate else ""
        symbols = {"info": "*", "ok": "+", "warn": "!", "err": "!"}
        print(f"{prefix}[{symbols.get(level, '*')}] {message}")
    
    def _setup_signal_handler(self):
        """Setup graceful interrupt handling"""
        def handler(signum, frame):
            self._interrupted = True
            print("\n\n[!] Interrupt received! Cleaning up...")
            self._emergency_cleanup()
            sys.exit(1)
        
        self._original_sigint = signal.getsignal(signal.SIGINT)
        signal.signal(signal.SIGINT, handler)
    
    def _restore_signal_handler(self):
        """Restore original signal handler"""
        signal.signal(signal.SIGINT, self._original_sigint)
    
    def _emergency_cleanup(self):
        """Cleanup temporary files on interrupt"""
        if self._backup_file_tmp and self._backup_file_tmp.exists():
            try:
                self._backup_file_tmp.unlink()
                self._log(f"Removed incomplete backup: {self._backup_file_tmp}")
            except Exception:
                pass
    
    def _check_disk_space(self, required_bytes: int) -> Tuple[bool, int]:
        """Check if enough disk space is available"""
        try:
            free_space = shutil.disk_usage(self.backup_dir).free
            # Require 10% margin
            has_space = free_space >= required_bytes * 1.1
            return has_space, free_space
        except Exception:
            # If we can't check, assume OK and let it fail later
            return True, 0
    
    def _progress_bar(self, current: int, total: int, start_time: float, 
                      extra_info: str = "") -> str:
        """Generate a nice progress bar with ETA"""
        if total == 0:
            return ""
        
        percent = current / total
        filled = int(PROGRESS_BAR_WIDTH * percent)
        bar = "█" * filled + "░" * (PROGRESS_BAR_WIDTH - filled)
        
        # Calculate ETA
        elapsed = time.time() - start_time
        if current > 0 and percent < 1:
            eta_seconds = (elapsed / current) * (total - current)
            if eta_seconds > 3600:
                eta_str = f"{eta_seconds/3600:.1f}h"
            elif eta_seconds > 60:
                eta_str = f"{eta_seconds/60:.1f}m"
            else:
                eta_str = f"{eta_seconds:.0f}s"
            eta_display = f" | ETA: {eta_str}"
        else:
            eta_display = ""
        
        extra = f" | {extra_info}" if extra_info else ""
        
        return f"\r[{bar}] {percent*100:5.1f}% ({current}/{total}){eta_display}{extra}    "
    
    def _print_progress(self, current: int, total: int, start_time: float,
                        extra_info: str = ""):
        """Print progress bar (overwrites current line)"""
        print(self._progress_bar(current, total, start_time, extra_info), end="", flush=True)
    
    def initialize(self) -> bool:
        """Initialize device and gather basic info"""
        self._log(f"Initializing device: {self.device_path}")
        self._log(f"Random seed: {self.seed}")
        
        if self.simulate:
            self._log("SIMULATE MODE: No actual I/O will be performed", "warn")
        
        if not os.path.exists(self.device_path):
            self._log(f"Device not found: {self.device_path}", "err")
            return False
        
        if not self.simulate:
            has_perms, perm_msg = self.check_permissions(self.device_path)
            if not has_perms:
                print(perm_msg)
                return False
        
        try:
            with open(self.device_path, 'rb') as f:
                f.seek(0, 2)
                self.device_size = f.tell()
                self.sector_count = self.device_size // SECTOR_SIZE
                
                if self.device_size >= 8192:
                    f.seek(0)
                    start_data = f.read(4096)
                    f.seek(-4096, 2)
                    end_data = f.read(4096)
                    self.device_id = hashlib.sha256(start_data + end_data).hexdigest()[:16]
                else:
                    f.seek(0)
                    self.device_id = hashlib.sha256(f.read()).hexdigest()[:16]
            
            self._log(f"Device size: {self.device_size / (1024**3):.2f} GB", "ok")
            self._log(f"Total sectors: {self.sector_count}", "ok")
            self._log(f"Device ID: {self.device_id}", "ok")
            
            self.results['total_sectors'] = self.sector_count
            return True
            
        except PermissionError:
            _, perm_msg = self.check_permissions(self.device_path)
            print(perm_msg)
            return False
        except Exception as e:
            self._log(f"Error initializing device: {e}", "err")
            return False
    
    def select_test_sectors(self, num_sectors: int, inversion_pct: float = 5, 
                           walking_pct: float = 2) -> List[int]:
        """Select sectors with test type assignment"""
        self._log(f"Selecting {num_sectors} sectors for testing...")
        
        rng = random.Random(self.seed)
        
        if num_sectors <= 0 or self.sector_count == 0:
            self._log("Invalid num_sectors or device not initialized", "err")
            return []
        
        if num_sectors > self.sector_count:
            self._log(f"Adjusting to {self.sector_count} sectors (device limit)", "warn")
            num_sectors = self.sector_count
        
        test_sectors = set()
        max_sector = self.sector_count - 1
        
        # Stratified (60%) + Random (40%)
        stratified_count = int(num_sectors * 0.6)
        random_count = num_sectors - stratified_count
        
        # Stratified sampling
        if stratified_count > 0:
            step = max(1, self.sector_count // stratified_count)
            for i in range(0, self.sector_count, step):
                test_sectors.add(i)
                if len(test_sectors) >= stratified_count:
                    break
        
        # Random sampling
        attempts = 0
        max_attempts = random_count * 10
        while len(test_sectors) < num_sectors and attempts < max_attempts:
            s = rng.randint(0, max_sector)
            test_sectors.add(s)
            attempts += 1
        
        self.test_sectors = sorted(test_sectors)
        
        # Assign test types to sectors
        num_inversion = int(len(self.test_sectors) * inversion_pct / 100)
        num_walking = int(len(self.test_sectors) * walking_pct / 100)
        
        # Shuffle for random assignment
        shuffled = self.test_sectors.copy()
        rng.shuffle(shuffled)
        
        inversion_sectors = set(shuffled[:num_inversion])
        walking_sectors = set(shuffled[num_inversion:num_inversion + num_walking])
        
        # Initialize metadata for each sector
        for sector in self.test_sectors:
            if sector in inversion_sectors:
                test_type = 'inversion'
            elif sector in walking_sectors:
                test_type = 'walking'
            else:
                test_type = 'standard'
            
            self.sector_metadata[sector] = {
                'test_type': test_type,
                'pattern_type': None,
                'pattern_seed_offset': None,
                'write_latency': None,
                'read_latency': None,
                'bit_mismatches': 0,
                'verified': None,
                'inversion_cycles': 0 if test_type == 'inversion' else None,
                'walking_errors': [] if test_type == 'walking' else None
            }
        
        self.results['tested_sectors'] = len(self.test_sectors)
        
        self._log(f"Selected {len(self.test_sectors)} sectors", "ok")
        self._log(f"  Standard: {len(self.test_sectors) - num_inversion - num_walking}")
        self._log(f"  Inversion (P→~P→P): {num_inversion}")
        self._log(f"  Walking bit: {num_walking}")
        
        return self.test_sectors
    
    def _generate_random_pattern(self, rng: random.Random) -> bytes:
        """Generate random pattern"""
        return bytes(rng.getrandbits(8) for _ in range(SECTOR_SIZE))
    
    def _generate_walking_pattern(self, position: int) -> bytes:
        """Generate walking-1 pattern (single bit set at position)"""
        pattern = bytearray(SECTOR_SIZE)
        byte_pos = position // 8
        bit_pos = position % 8
        if byte_pos < SECTOR_SIZE:
            pattern[byte_pos] = 1 << bit_pos
        return bytes(pattern)
    
    def _invert_pattern(self, pattern: bytes) -> bytes:
        """Invert all bits in pattern"""
        return bytes(~b & 0xFF for b in pattern)
    
    def backup_sectors(self) -> bool:
        """Backup original data from test sectors with space check and atomic write"""
        self._log(f"Backing up {len(self.test_sectors)} sectors...")
        
        if self.simulate:
            self._log("SIMULATE: Would backup sectors to disk", "ok")
            return True
        
        # Calculate required space (sectors + metadata estimate + margin)
        required_bytes = len(self.test_sectors) * SECTOR_SIZE + 8192  # +8KB for metadata
        has_space, free_space = self._check_disk_space(required_bytes)
        
        if not has_space:
            self._log(f"Insufficient disk space in {self.backup_dir}", "err")
            self._log(f"  Required: {required_bytes / 1024:.1f} KB", "err")
            self._log(f"  Available: {free_space / 1024:.1f} KB", "err")
            self._log(f"  Use --backup-dir to specify a different location", "info")
            return False
        
        self._log(f"Disk space OK: {free_space / 1024 / 1024:.1f} MB available")
        
        # Use temporary file for atomic write
        self._backup_file = self.backup_dir / f"backup_{self.session_timestamp}.dat"
        self._backup_file_tmp = self.backup_dir / f"backup_{self.session_timestamp}.dat.tmp"
        self._metadata_file = self.backup_dir / f"metadata_{self.session_timestamp}.json"
        
        # Setup interrupt handler
        self._setup_signal_handler()
        
        try:
            total_sectors = len(self.test_sectors)
            start_time = time.time()
            backup_offset = 0  # Track actual offset in backup file
            
            with open(self.device_path, 'rb') as dev, open(self._backup_file_tmp, 'wb') as backup:
                for idx, sector_num in enumerate(self.test_sectors):
                    if idx % 50 == 0 or idx == total_sectors - 1:
                        self._print_progress(idx + 1, total_sectors, start_time, f"sector {sector_num}")
                    
                    offset = sector_num * SECTOR_SIZE
                    dev.seek(offset)
                    data = dev.read(SECTOR_SIZE)
                    
                    if len(data) != SECTOR_SIZE:
                        self._log(f"\nWarning: Could not read full sector {sector_num}", "warn")
                        # Don't skip - this could cause offset mismatch
                        # Pad with zeros instead
                        data = data.ljust(SECTOR_SIZE, b'\x00')
                    
                    data_hash = hashlib.sha256(data).hexdigest()
                    backup.write(data)
                    
                    self.backup_data[sector_num] = {
                        'offset_in_backup': backup_offset,
                        'hash': data_hash
                    }
                    backup_offset += SECTOR_SIZE
                
                # Ensure all data is written
                backup.flush()
                os.fsync(backup.fileno())
            
            print()  # New line after progress bar
            
            # Verify the temp file was written correctly
            actual_size = self._backup_file_tmp.stat().st_size
            expected_size = len(self.test_sectors) * SECTOR_SIZE
            if actual_size != expected_size:
                raise IOError(f"Backup size mismatch: expected {expected_size}, got {actual_size}")
            
            # Calculate hash of completed backup
            backup_file_hash = self._calculate_file_hash(self._backup_file_tmp)
            
            # Write metadata
            with open(self._metadata_file, 'w') as f:
                json.dump({
                    'device': self.device_path,
                    'device_id': self.device_id,
                    'backup_file': str(self._backup_file),
                    'backup_file_hash': backup_file_hash,
                    'timestamp': datetime.now().isoformat(),
                    'session_timestamp': self.session_timestamp,
                    'seed': self.seed,
                    'sectors': self.backup_data
                }, f, indent=2)
            
            # Atomic rename: only if everything succeeded
            self._backup_file_tmp.rename(self._backup_file)
            self._backup_file_tmp = None  # Clear so cleanup doesn't try to delete
            
            self._log(f"Backup completed: {self._backup_file}", "ok")
            self._log(f"Backup hash: {backup_file_hash[:16]}...", "ok")
            self._log(f"Backup size: {actual_size / 1024:.1f} KB", "ok")
            return True
            
        except Exception as e:
            self._log(f"Backup failed: {e}", "err")
            # Cleanup incomplete files
            if self._backup_file_tmp and self._backup_file_tmp.exists():
                try:
                    self._backup_file_tmp.unlink()
                    self._log("Removed incomplete backup file", "info")
                except Exception:
                    pass
            if self._metadata_file and self._metadata_file.exists():
                try:
                    self._metadata_file.unlink()
                except Exception:
                    pass
            return False
        
        finally:
            self._restore_signal_handler()
    
    def _calculate_file_hash(self, filepath: Path) -> str:
        """Calculate SHA256 hash of a file"""
        sha256 = hashlib.sha256()
        with open(filepath, 'rb') as f:
            for chunk in iter(lambda: f.read(8192), b''):
                sha256.update(chunk)
        return sha256.hexdigest()
    
    def _write_sector(self, sector_num: int, pattern: bytes) -> Tuple[bool, float]:
        """Write pattern to sector"""
        if self.simulate:
            # Simulate latency
            return True, random.uniform(0.005, 0.015)
        
        try:
            start_time = time.perf_counter()
            with open(self.device_path, 'r+b') as dev:
                dev.seek(sector_num * SECTOR_SIZE)
                dev.write(pattern)
                dev.flush()
                os.fsync(dev.fileno())
            return True, time.perf_counter() - start_time
        except Exception as e:
            self._log(f"Write error at sector {sector_num}: {e}", "err")
            return False, 0.0
    
    def _read_sector(self, sector_num: int) -> Tuple[Optional[bytes], float]:
        """Read sector data"""
        if self.simulate:
            # Return simulated data
            return b'\x00' * SECTOR_SIZE, random.uniform(0.002, 0.008)
        
        try:
            start_time = time.perf_counter()
            with open(self.device_path, 'rb') as dev:
                dev.seek(sector_num * SECTOR_SIZE)
                data = dev.read(SECTOR_SIZE)
            return data, time.perf_counter() - start_time
        except Exception as e:
            self._log(f"Read error at sector {sector_num}: {e}", "err")
            return None, 0.0
    
    def _count_bit_mismatches(self, data: bytes, expected: bytes) -> int:
        """Count bit differences between data and expected"""
        mismatches = 0
        for i in range(min(len(data), len(expected))):
            if data[i] != expected[i]:
                mismatches += bin(data[i] ^ expected[i]).count('1')
        return mismatches
    
    def _test_sector_standard(self, sector_num: int, pattern: bytes, 
                              pattern_type: str, seed_offset: int) -> Dict:
        """Standard single write/read test"""
        meta = self.sector_metadata[sector_num]
        meta['pattern_type'] = pattern_type
        meta['pattern_seed_offset'] = seed_offset
        
        # Write
        write_ok, write_lat = self._write_sector(sector_num, pattern)
        meta['write_latency'] = write_lat
        
        if not write_ok:
            meta['verified'] = False
            return {'write_error': True}
        
        # Read and verify
        data, read_lat = self._read_sector(sector_num)
        meta['read_latency'] = read_lat
        
        if data is None:
            meta['verified'] = False
            return {'read_error': True}
        
        if self.simulate:
            meta['verified'] = True
            meta['bit_mismatches'] = 0
            return {'verified': True, 'bit_mismatches': 0}
        
        mismatches = self._count_bit_mismatches(data, pattern)
        meta['bit_mismatches'] = mismatches
        meta['verified'] = (mismatches == 0)
        
        return {
            'verified': meta['verified'],
            'bit_mismatches': mismatches,
            'write_latency': write_lat,
            'read_latency': read_lat
        }
    
    def _test_sector_inversion(self, sector_num: int, pattern: bytes,
                                pattern_type: str, seed_offset: int) -> Dict:
        """Inversion stress test: P → ~P → P"""
        meta = self.sector_metadata[sector_num]
        meta['pattern_type'] = pattern_type
        meta['pattern_seed_offset'] = seed_offset
        
        total_mismatches = 0
        total_write_lat = 0
        total_read_lat = 0
        cycles = 3  # P, ~P, P
        
        patterns = [pattern, self._invert_pattern(pattern), pattern]
        
        for cycle, p in enumerate(patterns):
            write_ok, write_lat = self._write_sector(sector_num, p)
            total_write_lat += write_lat
            
            if not write_ok:
                meta['verified'] = False
                meta['inversion_cycles'] = cycle
                return {'write_error': True, 'cycle': cycle}
            
            data, read_lat = self._read_sector(sector_num)
            total_read_lat += read_lat
            
            if data is None:
                meta['verified'] = False
                meta['inversion_cycles'] = cycle
                return {'read_error': True, 'cycle': cycle}
            
            if not self.simulate:
                mismatches = self._count_bit_mismatches(data, p)
                total_mismatches += mismatches
        
        meta['write_latency'] = total_write_lat / cycles
        meta['read_latency'] = total_read_lat / cycles
        meta['bit_mismatches'] = total_mismatches
        meta['inversion_cycles'] = cycles
        meta['verified'] = (total_mismatches == 0)
        
        return {
            'verified': meta['verified'],
            'bit_mismatches': total_mismatches,
            'cycles': cycles,
            'write_latency': total_write_lat / cycles,
            'read_latency': total_read_lat / cycles
        }
    
    def _test_sector_walking(self, sector_num: int) -> Dict:
        """Walking bit test to find directional bit errors"""
        meta = self.sector_metadata[sector_num]
        meta['pattern_type'] = 'walking'
        
        walking_errors = []
        total_write_lat = 0
        total_read_lat = 0
        
        # Test 8 bit positions (one per byte position, spread across sector)
        test_positions = [i * (SECTOR_SIZE * 8 // 8) for i in range(8)]
        
        for pos in test_positions:
            pattern = self._generate_walking_pattern(pos)
            
            write_ok, write_lat = self._write_sector(sector_num, pattern)
            total_write_lat += write_lat
            
            if not write_ok:
                walking_errors.append({'position': pos, 'error': 'write_failed'})
                continue
            
            data, read_lat = self._read_sector(sector_num)
            total_read_lat += read_lat
            
            if data is None:
                walking_errors.append({'position': pos, 'error': 'read_failed'})
                continue
            
            if not self.simulate and data != pattern:
                mismatches = self._count_bit_mismatches(data, pattern)
                walking_errors.append({
                    'position': pos,
                    'error': 'mismatch',
                    'bit_mismatches': mismatches
                })
        
        num_tests = len(test_positions)
        meta['write_latency'] = total_write_lat / num_tests if num_tests > 0 else 0
        meta['read_latency'] = total_read_lat / num_tests if num_tests > 0 else 0
        meta['walking_errors'] = walking_errors
        meta['bit_mismatches'] = sum(e.get('bit_mismatches', 0) for e in walking_errors)
        meta['verified'] = len(walking_errors) == 0
        
        return {
            'verified': meta['verified'],
            'walking_errors': walking_errors,
            'positions_tested': num_tests,
            'write_latency': meta['write_latency'],
            'read_latency': meta['read_latency']
        }
    
    def run_basic_test(self) -> Dict:
        """Run tests on all selected sectors"""
        print()
        self._log("Running integrity tests...")
        self._log("NOTE: Testing LOGICAL sectors (LBA). Controller may remap internally.")
        
        pattern_rng = random.Random(self.seed + 12345)
        
        test_results = {
            'write_errors': 0,
            'read_errors': 0,
            'verify_errors': 0,
            'bit_mismatches': 0,
            'write_latencies': [],
            'read_latencies': [],
            'slow_sectors': [],
            'patterns_used': {'classic': 0, 'random': 0, 'inversion': 0, 'walking': 0},
            'inversion_stats': {'tested': 0, 'failed': 0},
            'walking_stats': {'tested': 0, 'errors': 0}
        }
        
        total = len(self.test_sectors)
        start_time = time.time()
        errors_so_far = 0
        
        print()  # New line for progress bar
        
        for idx, sector_num in enumerate(self.test_sectors):
            # Update progress bar every sector
            test_type = self.sector_metadata[sector_num]['test_type']
            extra = f"sector {sector_num} ({test_type[0].upper()})"
            if errors_so_far > 0:
                extra += f" | err:{errors_so_far}"
            self._print_progress(idx, total, start_time, extra)
            
            meta = self.sector_metadata[sector_num]
            test_type = meta['test_type']
            
            # Generate pattern
            seed_offset = idx
            if pattern_rng.random() < 0.5:
                pattern_name = pattern_rng.choice(list(PATTERN_TYPES.keys()))
                pattern = PATTERN_TYPES[pattern_name]
                pattern_type = f'classic_{pattern_name}'
            else:
                pattern = self._generate_random_pattern(pattern_rng)
                pattern_type = 'random'
            
            # Execute appropriate test
            if test_type == 'inversion':
                result = self._test_sector_inversion(sector_num, pattern, pattern_type, seed_offset)
                test_results['patterns_used']['inversion'] += 1
                test_results['inversion_stats']['tested'] += 1
                if not result.get('verified', False):
                    test_results['inversion_stats']['failed'] += 1
                    
            elif test_type == 'walking':
                result = self._test_sector_walking(sector_num)
                test_results['patterns_used']['walking'] += 1
                test_results['walking_stats']['tested'] += 1
                if result.get('walking_errors'):
                    test_results['walking_stats']['errors'] += len(result['walking_errors'])
                    
            else:  # standard
                result = self._test_sector_standard(sector_num, pattern, pattern_type, seed_offset)
                if 'classic' in pattern_type:
                    test_results['patterns_used']['classic'] += 1
                else:
                    test_results['patterns_used']['random'] += 1
            
            # Aggregate results
            if result.get('write_error'):
                test_results['write_errors'] += 1
                errors_so_far += 1
                continue
            if result.get('read_error'):
                test_results['read_errors'] += 1
                errors_so_far += 1
                continue
            
            if not result.get('verified', True):
                test_results['verify_errors'] += 1
                errors_so_far += 1
                test_results['bit_mismatches'] += result.get('bit_mismatches', 0)
                self.results['errors'].append({
                    'sector': sector_num,
                    'type': 'bit_mismatch',
                    'test_type': test_type,
                    'count': result.get('bit_mismatches', 0)
                })
            
            # Collect latencies
            if 'write_latency' in result:
                test_results['write_latencies'].append(result['write_latency'])
            if 'read_latency' in result:
                test_results['read_latencies'].append(result['read_latency'])
            
            # Slow sector detection
            read_lat = result.get('read_latency', 0)
            if read_lat > 0.1:
                test_results['slow_sectors'].append({
                    'sector': sector_num,
                    'read_latency': read_lat,
                    'test_type': test_type
                })
        
        # Complete progress bar
        self._print_progress(total, total, start_time, "done!")
        print()  # New line after progress bar
        print()
        
        self._log("Test completed", "ok")
        self._log(f"  Write errors: {test_results['write_errors']}")
        self._log(f"  Verify errors: {test_results['verify_errors']}")
        self._log(f"  Bit mismatches (post-ECC): {test_results['bit_mismatches']}")
        self._log(f"  Slow sectors: {len(test_results['slow_sectors'])}")
        self._log(f"  Patterns: {test_results['patterns_used']}")
        self._log(f"  Inversion tests: {test_results['inversion_stats']}")
        self._log(f"  Walking tests: {test_results['walking_stats']}")
        
        return test_results
    
    def run_statistical_analysis(self, test_results: Dict) -> Dict:
        """Analyze test results statistically"""
        print()
        self._log("Running statistical analysis...")
        
        analysis = {}
        
        if test_results['read_latencies']:
            read_lats = test_results['read_latencies']
            analysis['read_latency'] = {
                'mean': statistics.mean(read_lats),
                'median': statistics.median(read_lats),
                'stdev': statistics.stdev(read_lats) if len(read_lats) > 1 else 0,
                'min': min(read_lats),
                'max': max(read_lats),
                'p95': sorted(read_lats)[int(len(read_lats) * 0.95)] if read_lats else 0
            }
        
        if test_results['write_latencies']:
            write_lats = test_results['write_latencies']
            analysis['write_latency'] = {
                'mean': statistics.mean(write_lats),
                'median': statistics.median(write_lats),
                'stdev': statistics.stdev(write_lats) if len(write_lats) > 1 else 0,
                'min': min(write_lats),
                'max': max(write_lats),
                'p95': sorted(write_lats)[int(len(write_lats) * 0.95)] if write_lats else 0
            }
        
        total_tested = len(self.test_sectors)
        total_bits_tested = total_tested * SECTOR_SIZE * 8
        analysis['error_rates'] = {
            'write_error_rate': test_results['write_errors'] / total_tested if total_tested > 0 else 0,
            'verify_error_rate': test_results['verify_errors'] / total_tested if total_tested > 0 else 0,
            'logical_bit_mismatch_rate': test_results['bit_mismatches'] / total_bits_tested if total_bits_tested > 0 else 0
        }
        
        # Additional analysis for special tests
        analysis['inversion_failure_rate'] = (
            test_results['inversion_stats']['failed'] / test_results['inversion_stats']['tested']
            if test_results['inversion_stats']['tested'] > 0 else 0
        )
        analysis['walking_error_rate'] = (
            test_results['walking_stats']['errors'] / (test_results['walking_stats']['tested'] * 8)
            if test_results['walking_stats']['tested'] > 0 else 0
        )
        
        self._log(f"Mean read latency: {analysis['read_latency']['mean']*1000:.2f} ms", "ok")
        self._log(f"Logical Bit Mismatch Rate (post-ECC): {analysis['error_rates']['logical_bit_mismatch_rate']:.2e}", "ok")
        if test_results['inversion_stats']['tested'] > 0:
            self._log(f"Inversion failure rate: {analysis['inversion_failure_rate']:.2%}", "ok")
        if test_results['walking_stats']['tested'] > 0:
            self._log(f"Walking error rate: {analysis['walking_error_rate']:.2%}", "ok")
        
        return analysis
    
    def calculate_health_score(self, test_results: Dict, analysis: Dict) -> Tuple[float, str]:
        """Calculate heuristic health score"""
        print()
        self._log("Calculating health score (heuristic)...")
        
        score = 100.0
        
        # Basic penalties
        score -= test_results['write_errors'] * 5
        score -= test_results['verify_errors'] * 10
        score -= min(test_results['bit_mismatches'] / 100, 20)
        
        # Slow sectors
        score -= min(len(test_results['slow_sectors']) / 10, 15)
        
        # Latency variance
        if 'read_latency' in analysis and analysis['read_latency']['stdev'] > 0.01:
            score -= min(analysis['read_latency']['stdev'] * 1000, 10)
        
        # Inversion failures (severe)
        score -= test_results['inversion_stats']['failed'] * 15
        
        # Walking errors (moderate)
        score -= min(test_results['walking_stats']['errors'] * 2, 10)
        
        score = max(0.0, min(100.0, score))
        
        if score >= 90:
            status = "EXCELLENT"
        elif score >= 75:
            status = "GOOD"
        elif score >= 50:
            status = "FAIR"
        elif score >= 25:
            status = "POOR"
        else:
            status = "CRITICAL"
        
        self._log(f"Health Score: {score:.1f}/100 ({status})", "ok")
        
        return score, status
    
    def _restore_single_sector(self, dev, sector_num: int, original_data: bytes) -> bool:
        """Restore single sector with fsync"""
        try:
            dev.seek(sector_num * SECTOR_SIZE)
            dev.write(original_data)
            dev.flush()
            os.fsync(dev.fileno())
            return True
        except Exception:
            return False
    
    def _verify_single_sector(self, dev, sector_num: int, expected_hash: str) -> bool:
        """Verify single sector matches hash"""
        try:
            dev.seek(sector_num * SECTOR_SIZE)
            data = dev.read(SECTOR_SIZE)
            return hashlib.sha256(data).hexdigest() == expected_hash
        except Exception:
            return False
    
    def restore_sectors(self) -> bool:
        """Restore with aggressive retry strategy"""
        print()
        self._log("Restoring original data...")
        
        if self.simulate:
            self._log("SIMULATE: Would restore all sectors from backup", "ok")
            return True
        
        backup_file = self.backup_dir / f"backup_{self.session_timestamp}.dat"
        metadata_file = self.backup_dir / f"metadata_{self.session_timestamp}.json"
        
        if not backup_file.exists() or not metadata_file.exists():
            self._log("Session backup not found, searching for most recent...", "warn")
            backup_files = sorted(self.backup_dir.glob("backup_*.dat"))
            metadata_files = sorted(self.backup_dir.glob("metadata_*.json"))
            
            if not backup_files or not metadata_files:
                self._log("No backup files found", "err")
                return False
            
            backup_file = backup_files[-1]
            metadata_file = metadata_files[-1]
            self._log(f"Using backup: {backup_file.name}")
        
        try:
            with open(metadata_file, 'r') as f:
                metadata = json.load(f)
            
            # Verify backup integrity
            if 'backup_file_hash' in metadata:
                self._log("Verifying backup file integrity...")
                current_hash = self._calculate_file_hash(backup_file)
                if current_hash != metadata['backup_file_hash']:
                    self._log("CRITICAL: Backup file is corrupted!", "err")
                    return False
                self._log("Backup file integrity verified", "ok")
            
            # Check device identity
            if 'device_id' in metadata and self.device_id:
                if metadata['device_id'] != self.device_id:
                    self._log("WARNING: Device identity mismatch!", "warn")
                    response = input("[?] Continue anyway? (yes/no): ")
                    if response.lower() != 'yes':
                        return False
            
            # Load backup data
            with open(backup_file, 'rb') as backup:
                sector_data = {}
                for sector_str, info in metadata['sectors'].items():
                    sector_num = int(sector_str)
                    backup.seek(info['offset_in_backup'])
                    sector_data[sector_num] = {
                        'data': backup.read(SECTOR_SIZE),
                        'hash': info['hash']
                    }
            
            # Phase 1: Batch restore
            self._log("Phase 1: Restoring all sectors...")
            failed_sectors = []
            total_sectors = len(sector_data)
            start_time = time.time()
            
            with open(self.device_path, 'r+b') as dev:
                for idx, (sector_num, sdata) in enumerate(sector_data.items()):
                    if idx % 50 == 0 or idx == total_sectors - 1:
                        self._print_progress(idx + 1, total_sectors, start_time, f"sector {sector_num}")
                    if not self._restore_single_sector(dev, sector_num, sdata['data']):
                        failed_sectors.append(sector_num)
            
            print()  # New line after progress bar
            
            if not failed_sectors:
                self._log(f"Phase 1 complete: All {len(sector_data)} sectors restored", "ok")
            else:
                self._log(f"Phase 1: {len(failed_sectors)} sectors failed", "warn")
            
            # Phase 2: Aggressive retry
            if failed_sectors:
                self._log(f"Phase 2: Aggressive retry for {len(failed_sectors)} sectors...")
                still_failed = []
                
                for sector_num in failed_sectors:
                    success = False
                    sdata = sector_data[sector_num]
                    
                    for attempt in range(RESTORE_MAX_RETRIES):
                        time.sleep(RESTORE_RETRY_DELAY * (attempt + 1))
                        try:
                            with open(self.device_path, 'r+b') as dev:
                                if self._restore_single_sector(dev, sector_num, sdata['data']):
                                    if self._verify_single_sector(dev, sector_num, sdata['hash']):
                                        success = True
                                        break
                        except Exception:
                            continue
                    
                    if not success:
                        still_failed.append(sector_num)
                
                failed_sectors = still_failed
            
            # Phase 3: Final verification
            self._log("Phase 3: Final verification...")
            verify_failed = []
            start_time = time.time()
            
            with open(self.device_path, 'rb') as dev:
                for idx, (sector_num, sdata) in enumerate(sector_data.items()):
                    if idx % 100 == 0 or idx == total_sectors - 1:
                        self._print_progress(idx + 1, total_sectors, start_time, f"verifying {sector_num}")
                    if not self._verify_single_sector(dev, sector_num, sdata['hash']):
                        if sector_num not in failed_sectors:
                            verify_failed.append(sector_num)
            
            print()  # New line after progress bar
            
            all_failed = list(set(failed_sectors + verify_failed))
            
            if not all_failed:
                self._log(f"All {len(sector_data)} sectors restored and verified", "ok")
                return True
            
            # Phase 4: Recovery script
            self._log(f"CRITICAL: {len(all_failed)} sectors could not be restored!", "err")
            recovery_script = self._generate_recovery_script(backup_file, all_failed, sector_data)
            
            print(f"\n{'!'*60}")
            print("RESTORE INCOMPLETE")
            print(f"{'!'*60}")
            print(f"Failed sectors: {all_failed}")
            print(f"Recovery script: {recovery_script}")
            print(f"{'!'*60}")
            
            return False
            
        except Exception as e:
            self._log(f"Restore failed: {e}", "err")
            return False
    
    def _generate_recovery_script(self, backup_file: Path, failed_sectors: List[int], 
                                   sector_data: Dict) -> Path:
        """Generate bash recovery script"""
        script_path = self.backup_dir / f"recover_{self.session_timestamp}.sh"
        
        script = f'''#!/bin/bash
# SafeSDTester Emergency Recovery
# Generated: {datetime.now().isoformat()}
# Device: {self.device_path}

DEVICE="{self.device_path}"
BACKUP="{backup_file}"

if [ "$EUID" -ne 0 ]; then
    echo "Run as root (sudo)"
    exit 1
fi

echo "Recovering {len(failed_sectors)} sectors..."
'''
        
        for sector_num in failed_sectors:
            if sector_num in sector_data:
                offset = list(sector_data.keys()).index(sector_num) * SECTOR_SIZE
                script += f'dd if="$BACKUP" of="$DEVICE" bs={SECTOR_SIZE} count=1 skip={offset // SECTOR_SIZE} seek={sector_num} conv=notrunc,fsync 2>/dev/null && echo "Sector {sector_num}: OK" || echo "Sector {sector_num}: FAILED"\n'
        
        script += '\necho "Done."\n'
        
        with open(script_path, 'w') as f:
            f.write(script)
        os.chmod(script_path, 0o755)
        
        return script_path
    
    def cleanup_backup(self):
        """Remove session backup files"""
        self._log("Cleaning up backup files...")
        
        if self.simulate:
            self._log("SIMULATE: Would remove backup files", "ok")
            return
        
        session_files = [
            self.backup_dir / f"backup_{self.session_timestamp}.dat",
            self.backup_dir / f"metadata_{self.session_timestamp}.json",
            self.backup_dir / f"report_{self.session_timestamp}.txt",
            self.backup_dir / f"report_{self.session_timestamp}.json",
            self.backup_dir / f"recover_{self.session_timestamp}.sh"
        ]
        
        removed = 0
        for f in session_files:
            if f.exists():
                f.unlink()
                removed += 1
        
        self._log(f"Cleanup completed ({removed} files)", "ok")
    
    def generate_report(self, analysis: Dict) -> str:
        """Generate text report"""
        r = []
        r.append("=" * 60)
        r.append("SD CARD HEALTH TEST REPORT")
        r.append("=" * 60)
        r.append(f"Device: {self.device_path}")
        r.append(f"Device ID: {self.device_id}")
        r.append(f"Test Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        r.append(f"Seed: {self.seed}")
        r.append(f"Simulate Mode: {self.simulate}")
        r.append(f"Total Sectors: {self.results['total_sectors']}")
        r.append(f"Tested Sectors: {self.results['tested_sectors']}")
        r.append("")
        r.append("HEALTH SCORE (Heuristic)")
        r.append("-" * 60)
        r.append(f"Score: {self.results['health_score']:.1f}/100 ({self.results['status']})")
        r.append("Note: Empirical estimate, not scientific metric")
        r.append("")
        
        if 'read_latency' in analysis:
            r.append("PERFORMANCE")
            r.append("-" * 60)
            r.append(f"Read Latency (mean): {analysis['read_latency']['mean']*1000:.2f} ms")
            r.append(f"Read Latency (p95): {analysis['read_latency']['p95']*1000:.2f} ms")
            r.append(f"Write Latency (mean): {analysis['write_latency']['mean']*1000:.2f} ms")
            r.append("")
        
        if 'error_rates' in analysis:
            r.append("ERROR RATES")
            r.append("-" * 60)
            r.append(f"Logical Bit Mismatch Rate: {analysis['error_rates']['logical_bit_mismatch_rate']:.2e}")
            r.append(f"Verify Error Rate: {analysis['error_rates']['verify_error_rate']:.2%}")
            if analysis.get('inversion_failure_rate', 0) > 0:
                r.append(f"Inversion Failure Rate: {analysis['inversion_failure_rate']:.2%}")
            if analysis.get('walking_error_rate', 0) > 0:
                r.append(f"Walking Error Rate: {analysis['walking_error_rate']:.2%}")
            r.append("")
        
        if self.results['errors']:
            r.append("ERRORS DETECTED")
            r.append("-" * 60)
            for error in self.results['errors'][:10]:
                r.append(f"  Sector {error['sector']}: {error['type']} ({error.get('count', 'N/A')} bits)")
            if len(self.results['errors']) > 10:
                r.append(f"  ... and {len(self.results['errors']) - 10} more")
            r.append("")
        
        r.append("RECOMMENDATIONS")
        r.append("-" * 60)
        score = self.results['health_score']
        if score >= 90:
            r.append("  Card in excellent condition.")
        elif score >= 75:
            r.append("  Card in good condition. Monitor periodically.")
        elif score >= 50:
            r.append("  Card shows wear. Backup more frequently.")
        elif score >= 25:
            r.append("  Card degrading. Plan replacement.")
        else:
            r.append("  Card critical. Replace immediately.")
        
        r.append("")
        r.append("TECHNICAL NOTES")
        r.append("-" * 60)
        r.append("  - Tests LOGICAL sectors (LBA)")
        r.append("  - Controller FTL may remap transparently")
        r.append("  - Errors are POST-ECC")
        r.append("=" * 60)
        
        return "\n".join(r)
    
    def save_forensic_report(self, analysis: Dict) -> Path:
        """Save complete JSON report with per-sector metadata"""
        report_path = self.backup_dir / f"report_{self.session_timestamp}.json"
        
        if self.simulate:
            self._log(f"SIMULATE: Would save forensic report to {report_path}")
            return report_path
        
        report = {
            'version': '2.2',
            'timestamp': datetime.now().isoformat(),
            'device': {
                'path': self.device_path,
                'id': self.device_id,
                'size_bytes': self.device_size,
                'sector_count': self.sector_count
            },
            'test_config': {
                'seed': self.seed,
                'sectors_tested': len(self.test_sectors),
                'simulate': self.simulate
            },
            'results': self.results,
            'analysis': analysis,
            'sector_metadata': {str(k): v for k, v in self.sector_metadata.items()}
        }
        
        with open(report_path, 'w') as f:
            json.dump(report, f, indent=2)
        
        self._log(f"Forensic report saved: {report_path}", "ok")
        return report_path
    
    def run_full_test(self, profile: str = 'standard', keep_backup: bool = False) -> bool:
        """Run complete test cycle"""
        self.results['start_time'] = datetime.now().isoformat()
        
        prof = PROFILES.get(profile, PROFILES['standard'])
        print(f"\n{'='*60}")
        print(f"SafeSDTester v2.3 - {profile.upper()} profile")
        print(f"{'='*60}")
        print(f"{prof['description']}")
        if self.simulate:
            print("*** SIMULATE MODE - NO ACTUAL I/O ***")
        print(f"{'='*60}\n")
        
        if not self.initialize():
            return False
        
        if not self.select_test_sectors(prof['sectors'], prof['inversion_pct'], prof['walking_pct']):
            return False
        
        if not self.backup_sectors():
            return False
        
        try:
            test_results = self.run_basic_test()
            analysis = self.run_statistical_analysis(test_results)
            
            score, status = self.calculate_health_score(test_results, analysis)
            self.results['health_score'] = score
            self.results['status'] = status
            self.results['performance'] = analysis
            
            print("\n" + self.generate_report(analysis))
            
            # Save reports (with error handling - don't let report failure block restore)
            if not self.simulate:
                try:
                    report_file = self.backup_dir / f"report_{self.session_timestamp}.txt"
                    with open(report_file, 'w') as f:
                        f.write(self.generate_report(analysis))
                    self._log(f"Text report saved: {report_file}", "ok")
                except Exception as e:
                    self._log(f"Warning: Could not save text report: {e}", "warn")
                
                try:
                    self.save_forensic_report(analysis)
                except Exception as e:
                    self._log(f"Warning: Could not save forensic report: {e}", "warn")
            
        finally:
            if not self.simulate:
                restore_success = self.restore_sectors()
                if restore_success and not keep_backup:
                    self.cleanup_backup()
            else:
                self._log("SIMULATE: Skipping restore (no changes made)", "ok")
        
        self.results['end_time'] = datetime.now().isoformat()
        return True


def main():
    parser = argparse.ArgumentParser(
        description='SafeSDTester v2.3 - SD Card Health Testing Tool',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Profiles:
  quick     - Fast test (~5 min), basic health check
  standard  - Balanced test (~30 min), good coverage [default]
  deep      - Thorough test (~2 hours), comprehensive
  forensic  - Laboratory test (~4+ hours), maximum coverage

Examples:
  sudo python3 sd_health_tester.py /dev/sdb
  sudo python3 sd_health_tester.py /dev/sdb --profile quick
  sudo python3 sd_health_tester.py /dev/sdb --simulate
  sudo python3 sd_health_tester.py /dev/sdb --profile forensic --seed 12345
        """
    )
    
    parser.add_argument('device', help='Device path (e.g., /dev/sdb)')
    parser.add_argument('--profile', choices=PROFILES.keys(), default='standard',
                       help='Test profile (default: standard)')
    parser.add_argument('--keep-backup', action='store_true',
                       help='Keep backup files after test')
    parser.add_argument('--backup-dir', default=BACKUP_DIR,
                       help=f'Backup directory (default: {BACKUP_DIR})')
    parser.add_argument('--seed', type=int, default=None,
                       help='Random seed for reproducibility')
    parser.add_argument('--simulate', '--dry-run', action='store_true',
                       help='Simulate test without writing to device')
    
    args = parser.parse_args()
    
    if not args.simulate:
        has_perms, perm_msg = SafeSDTester.check_permissions(args.device)
        if not has_perms:
            print(perm_msg)
            sys.exit(1)
    
    if not os.path.exists(args.device):
        print(f"[!] Device not found: {args.device}")
        sys.exit(1)
    
    # Confirmation
    prof = PROFILES[args.profile]
    print(f"\n{'='*60}")
    print("SafeSDTester v2.3 - Laboratory Edition")
    print(f"{'='*60}")
    print(f"Device: {args.device}")
    print(f"Profile: {args.profile} - {prof['description']}")
    print(f"Sectors: ~{prof['sectors']}")
    print(f"Inversion tests: {prof['inversion_pct']}%")
    print(f"Walking tests: {prof['walking_pct']}%")
    if args.simulate:
        print("\n*** SIMULATE MODE - NO WRITES ***")
    else:
        print("\nWARNING: This will write to the device.")
        print("Data will be backed up and restored.")
    print(f"{'='*60}")
    
    if not args.simulate:
        response = input("\nContinue? (yes/no): ")
        if response.lower() != 'yes':
            print("Aborted.")
            sys.exit(0)
    
    tester = SafeSDTester(args.device, args.backup_dir, args.seed, args.simulate)
    success = tester.run_full_test(args.profile, args.keep_backup)
    
    sys.exit(0 if success else 1)


if __name__ == '__main__':
    main()
