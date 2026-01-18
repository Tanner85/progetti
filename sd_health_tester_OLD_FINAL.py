#!/usr/bin/env python3
"""
SafeSDTester - SD Card Health Testing Tool
Test SD card integrity and predict failure without losing data

Version: 1.0
"""

import os
import sys
import time
import hashlib
import json
import random
import signal
import statistics
from pathlib import Path
from datetime import datetime
from typing import List, Dict, Tuple, Optional
import argparse

# tqdm per progress bar (fallback se non installato)
try:
    from tqdm import tqdm
    TQDM_AVAILABLE = True
except ImportError:
    TQDM_AVAILABLE = False
    tqdm = None

# Configurazione
SECTOR_SIZE = 512  # Standard sector size
MIN_TEST_SECTORS = 10000  # Minimo settori da testare (3k start + 4k random + 3k end)
BACKUP_DIR = "/tmp/sd_tester_backup"
PATTERNS = [
    b'\x00' * SECTOR_SIZE,  # All zeros
    b'\xFF' * SECTOR_SIZE,  # All ones
    b'\xAA' * SECTOR_SIZE,  # Alternating pattern
    b'\x55' * SECTOR_SIZE,  # Inverse alternating
]


class SafeSDTester:
    """Main class for safe SD card testing with backup/restore"""
    
    def __init__(self, device_path: str, backup_dir: str = BACKUP_DIR):
        self.device_path = device_path
        self.backup_dir = Path(backup_dir)
        self.backup_dir.mkdir(parents=True, exist_ok=True)
        
        self.device_size = 0
        self.sector_count = 0
        self.test_sectors = []
        self.backup_data = {}
        
        self.session_timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        
        self.device_id = None
        
        self._interrupted = False
        self._original_sigint_handler = None
        
        self.results = {
            'start_time': None,
            'end_time': None,
            'device': device_path,
            'total_sectors': 0,
            'tested_sectors': 0,
            'errors': [],
            'performance': {},
            'health_score': 0
        }
    
    def _handle_interrupt(self, signum, frame):
        """Handle CTRL+C gracefully"""
        if self._interrupted:
            # Secondo CTRL+C: forza uscita
            print("\n[!] Forced exit. Backup files preserved in:", self.backup_dir)
            sys.exit(1)
        
        self._interrupted = True
        print("\n\n" + "!"*60)
        print("[!] INTERRUPT RECEIVED - Stopping test gracefully...")
        print("[!] Press CTRL+C again to force exit (NOT RECOMMENDED)")
        print("[!] Restore will begin shortly...")
        print("!"*60 + "\n")
    
    def _install_signal_handler(self):
        """Install SIGINT handler for graceful interruption"""
        self._original_sigint_handler = signal.signal(signal.SIGINT, self._handle_interrupt)
    
    def _restore_signal_handler(self):
        """Restore original SIGINT handler"""
        if self._original_sigint_handler is not None:
            signal.signal(signal.SIGINT, self._original_sigint_handler)
        
    def initialize(self) -> bool:
        """Initialize device and gather basic info"""
        print(f"[*] Initializing device: {self.device_path}")
        
        if not os.path.exists(self.device_path):
            print(f"[!] Device not found: {self.device_path}")
            return False
            
        try:
            # Get device size
            with open(self.device_path, 'rb') as f:
                f.seek(0, 2)  # Seek to end
                self.device_size = f.tell()
                self.sector_count = self.device_size // SECTOR_SIZE
                
                #  Device identity (hash first 4KB + last 4KB)
                if self.device_size >= 8192:
                    f.seek(0)
                    start_data = f.read(4096)
                    f.seek(-4096, 2)
                    end_data = f.read(4096)
                    self.device_id = hashlib.sha256(start_data + end_data).hexdigest()[:16]
                else:
                    f.seek(0)
                    self.device_id = hashlib.sha256(f.read()).hexdigest()[:16]
                
            print(f"[+] Device size: {self.device_size / (1024**3):.2f} GB")
            print(f"[+] Total sectors: {self.sector_count}")
            print(f"[+] Device ID: {self.device_id}")
            
            self.results['total_sectors'] = self.sector_count
            return True
            
        except PermissionError:
            print(f"[!] Permission denied. Try running with sudo")
            return False
        except Exception as e:
            print(f"[!] Error initializing device: {e}")
            return False
    
    def select_test_sectors(self, num_sectors: int = MIN_TEST_SECTORS) -> List[int]:
        """Select sectors for testing with smart distribution"""
        print(f"[*] Selecting {num_sectors} sectors for testing...")

        # Validazione input
        if num_sectors <= 0 or self.sector_count == 0:
            print("[!] Invalid num_sectors or device not initialized")
            return []

        # Validazione num_sectors vs capacity
        if num_sectors > self.sector_count:
            print(f"[!] Requested {num_sectors} sectors but device has only {self.sector_count}")
            print(f"[!] Adjusting to test all {self.sector_count} sectors")
            num_sectors = self.sector_count

        test_sectors = set()

        start_count = int(num_sectors * 0.3)
        random_count = int(num_sectors * 0.4)
        end_count = num_sectors - start_count - random_count

        # Calcolo sicuro delle zone per device piccoli
        # Per device molto piccoli, riduciamo le zone proporzionalmente
        start_zone_size = min(max(1000, self.sector_count // 10), self.sector_count // 3)
        end_zone_size = start_zone_size
        
        # Assicuriamoci che ci sia spazio per la zona random
        middle_zone_start = start_zone_size
        middle_zone_end = self.sector_count - end_zone_size
        
        # Se device troppo piccolo per avere 3 zone distinte
        if middle_zone_end <= middle_zone_start:
            print(f"[!] Device too small for zone-based testing ({self.sector_count} sectors)")
            print(f"[!] Falling back to uniform distribution")
            # Fallback: distribuzione uniforme
            if num_sectors >= self.sector_count:
                self.test_sectors = list(range(self.sector_count))
            else:
                step = max(1, self.sector_count // num_sectors)
                self.test_sectors = list(range(0, self.sector_count, step))[:num_sectors]
            
            self.results['tested_sectors'] = len(self.test_sectors)
            print(f"[+] Selected {len(self.test_sectors)} sectors (uniform distribution)")
            return self.test_sectors

        # START ZONE
        if start_count > 0:
            step = max(1, start_zone_size // start_count)
            for i in range(0, start_zone_size, step):
                if len(test_sectors) >= start_count:
                    break
                test_sectors.add(i)

        # RANDOM ZONE (middle)
        # Check che la zona random sia valida
        if random_count > 0 and middle_zone_end > middle_zone_start:
            available_in_middle = middle_zone_end - middle_zone_start
            actual_random_count = min(random_count, available_in_middle)
            
            if actual_random_count < random_count:
                print(f"[!] Middle zone too small, reducing random sectors from {random_count} to {actual_random_count}")
            
            random_sectors = set()
            max_attempts = actual_random_count * 10  # Prevent infinite loop
            attempts = 0
            while len(random_sectors) < actual_random_count and attempts < max_attempts:
                s = random.randint(middle_zone_start, middle_zone_end - 1)
                random_sectors.add(s)
                attempts += 1
            
            test_sectors |= random_sectors

        # END ZONE
        end_zone_start = self.sector_count - end_zone_size
        if end_count > 0:
            step = max(1, end_zone_size // end_count)
            for i in range(end_zone_start, self.sector_count, step):
                if len([s for s in test_sectors if s >= end_zone_start]) >= end_count:
                    break
                test_sectors.add(i)

        self.test_sectors = sorted(test_sectors)
        self.results['tested_sectors'] = len(self.test_sectors)

        print(f"[+] Selected {len(self.test_sectors)} sectors")
        print(f"    Start zone: {len([s for s in self.test_sectors if s < start_zone_size])}")
        print(f"    Random zone: {len([s for s in self.test_sectors if start_zone_size <= s < end_zone_start])}")
        print(f"    End zone: {len([s for s in self.test_sectors if s >= end_zone_start])}")
        
        return self.test_sectors
    
    def backup_sectors(self) -> bool:
        """Backup original data from test sectors"""
        print(f"[*] Backing up {len(self.test_sectors)} sectors...")
        
        # Usa timestamp di sessione unico
        backup_file = self.backup_dir / f"backup_{self.session_timestamp}.dat"
        metadata_file = self.backup_dir / f"metadata_{self.session_timestamp}.json"
        
        try:
            with open(self.device_path, 'rb') as dev, open(backup_file, 'wb') as backup:
                # Progress bar
                if TQDM_AVAILABLE:
                    iterator = tqdm(self.test_sectors, desc="Backing up", unit="sector",
                                  ncols=80, bar_format='{l_bar}{bar}| {n_fmt}/{total_fmt} [{elapsed}<{remaining}]')
                else:
                    iterator = self.test_sectors
                
                for sector_num in iterator:
                    offset = sector_num * SECTOR_SIZE
                    dev.seek(offset)
                    data = dev.read(SECTOR_SIZE)
                    
                    if len(data) != SECTOR_SIZE:
                        print(f"[!] Warning: Could not read full sector {sector_num}")
                        continue
                    
                    # Calcola hash per verifica
                    data_hash = hashlib.sha256(data).hexdigest()
                    
                    # Salva dati
                    backup.write(data)
                    
                    # Salva metadata
                    self.backup_data[sector_num] = {
                        'offset_in_backup': len(self.backup_data) * SECTOR_SIZE,
                        'hash': data_hash
                    }
            
            # Calcola hash dell'intero backup file per verifica integrità
            backup_file_hash = self._calculate_file_hash(backup_file)
            
            # Salva metadata JSON
            with open(metadata_file, 'w') as f:
                json.dump({
                    'device': self.device_path,
                    'device_id': self.device_id,  
                    'backup_file': str(backup_file),
                    'backup_file_hash': backup_file_hash,  
                    'timestamp': datetime.now().isoformat(),
                    'session_timestamp': self.session_timestamp,
                    'sectors': self.backup_data
                }, f, indent=2)
            
            print(f"[+] Backup completed: {backup_file}")
            print(f"[+] Metadata saved: {metadata_file}")
            print(f"[+] Backup hash: {backup_file_hash[:16]}...")
            return True
            
        except Exception as e:
            print(f"[!] Backup failed: {e}")
            return False
    
    def _calculate_file_hash(self, filepath: Path) -> str:
        """Calculate SHA256 hash of a file"""
        sha256 = hashlib.sha256()
        with open(filepath, 'rb') as f:
            for chunk in iter(lambda: f.read(8192), b''):
                sha256.update(chunk)
        return sha256.hexdigest()
    
    def write_test_pattern(self, sector_num: int, pattern: bytes) -> Tuple[bool, float]:
        """Write test pattern to a sector and measure latency"""
        try:
            start_time = time.perf_counter()
            
            with open(self.device_path, 'r+b') as dev:
                offset = sector_num * SECTOR_SIZE
                dev.seek(offset)
                dev.write(pattern)
                dev.flush()
                os.fsync(dev.fileno())
            
            latency = time.perf_counter() - start_time
            return True, latency
            
        except Exception as e:
            print(f"[!] Write error at sector {sector_num}: {e}")
            return False, 0.0
    
    def read_and_verify(self, sector_num: int, expected_pattern: bytes) -> Tuple[bool, float, int]:
        """Read sector and verify pattern, count bit errors"""
        try:
            start_time = time.perf_counter()
            
            with open(self.device_path, 'rb') as dev:
                offset = sector_num * SECTOR_SIZE
                dev.seek(offset)
                data = dev.read(SECTOR_SIZE)
            
            latency = time.perf_counter() - start_time
            
            # Conta bit errors
            bit_errors = 0
            for i in range(min(len(data), len(expected_pattern))):
                if data[i] != expected_pattern[i]:
                    # Conta bit differenti nel byte
                    xor = data[i] ^ expected_pattern[i]
                    bit_errors += bin(xor).count('1')
            
            match = (data == expected_pattern)
            return match, latency, bit_errors
            
        except Exception as e:
            print(f"[!] Read error at sector {sector_num}: {e}")
            return False, 0.0, -1
    
    def run_basic_test(self) -> Dict:
        """Run basic write/read/verify test on selected sectors"""
        print("\n[*] Running basic integrity test...")
        
        test_results = {
            'write_errors': 0,
            'read_errors': 0,
            'verify_errors': 0,
            'bit_errors': 0,
            'write_latencies': [],
            'read_latencies': [],
            'slow_sectors': []
        }
        
        total = len(self.test_sectors)
        
        # Progress bar con tqdm o fallback
        if TQDM_AVAILABLE:
            iterator = tqdm(self.test_sectors, desc="Testing sectors", unit="sector",
                          ncols=80, bar_format='{l_bar}{bar}| {n_fmt}/{total_fmt} [{elapsed}<{remaining}]')
        else:
            iterator = self.test_sectors
            print("[*] Tip: install tqdm for a nicer progress bar (pip install tqdm)")
        
        for idx, sector_num in enumerate(iterator):
            # Check per interruzione CTRL+C
            if self._interrupted:
                print("\n[!] Test interrupted by user")
                if TQDM_AVAILABLE:
                    iterator.close()
                break
            
            # Fallback progress ogni 100 settori se no tqdm
            if not TQDM_AVAILABLE and idx % 100 == 0:
                progress = (idx / total) * 100
                print(f"[*] Progress: {progress:.1f}% ({idx+1}/{total})")
            
            # Seleziona pattern casuale
            pattern = random.choice(PATTERNS)
            
            # Write
            write_ok, write_lat = self.write_test_pattern(sector_num, pattern)
            if not write_ok:
                test_results['write_errors'] += 1
                continue
            
            test_results['write_latencies'].append(write_lat)
            
            # Read and verify
            verify_ok, read_lat, bit_errors = self.read_and_verify(sector_num, pattern)
            test_results['read_latencies'].append(read_lat)
            
            if not verify_ok:
                test_results['verify_errors'] += 1
                if bit_errors > 0:
                    test_results['bit_errors'] += bit_errors
                    self.results['errors'].append({
                        'sector': sector_num,
                        'type': 'bit_error',
                        'count': bit_errors
                    })
            
            # Identifica settori lenti (outlier)
            if read_lat > 0.1:  # > 100ms
                test_results['slow_sectors'].append({
                    'sector': sector_num,
                    'read_latency': read_lat,
                    'write_latency': write_lat
                })
        
        # Print finale 100% per fallback (se non interrotto)
        if not TQDM_AVAILABLE and not self._interrupted:
            print(f"[*] Progress: 100.0% ({total}/{total})")
        
        print(f"[+] Basic test completed")
        print(f"    Write errors: {test_results['write_errors']}")
        print(f"    Verify errors: {test_results['verify_errors']}")
        print(f"    Bit errors: {test_results['bit_errors']}")
        print(f"    Slow sectors: {len(test_results['slow_sectors'])}")
        
        return test_results
    
    def run_statistical_analysis(self, test_results: Dict) -> Dict:
        """Analyze test results statistically"""
        print("\n[*] Running statistical analysis...")
        
      
        analysis = {}
        
        # Latency statistics
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
        
        # Error rates
        total_tested = len(self.test_sectors)
        analysis['error_rates'] = {
            'write_error_rate': test_results['write_errors'] / total_tested if total_tested > 0 else 0,
            'verify_error_rate': test_results['verify_errors'] / total_tested if total_tested > 0 else 0,
            'bit_error_rate': test_results['bit_errors'] / (total_tested * SECTOR_SIZE * 8) if total_tested > 0 else 0
        }
        
        print(f"[+] Mean read latency: {analysis['read_latency']['mean']*1000:.2f} ms")
        print(f"[+] Bit Error Rate: {analysis['error_rates']['bit_error_rate']:.2e}")
        
        return analysis
    
    def calculate_health_score(self, test_results: Dict, analysis: Dict) -> Tuple[float, str]:
        """Calculate overall health score (0-100)"""
        print("\n[*] Calculating health score...")
        
        score = 100.0
        
        # Penalità per errori
        score -= test_results['write_errors'] * 5
        score -= test_results['verify_errors'] * 10
        score -= min(test_results['bit_errors'] / 100, 20)  # Max 20 punti
        
        # Penalità per settori lenti
        slow_sector_penalty = min(len(test_results['slow_sectors']) / 10, 15)
        score -= slow_sector_penalty
        
        # Penalità per alta variabilità latenza (segno di degrado)
        if 'read_latency' in analysis and analysis['read_latency']['stdev'] > 0.01:
            score -= min(analysis['read_latency']['stdev'] * 1000, 10)
        
        score = max(0.0, min(100.0, score))
        
        # Classificazione
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
        
        print(f"[+] Health Score: {score:.1f}/100 ({status})")
        
        return score, status
    
    def restore_sectors(self) -> bool:
        """Restore original data from backup"""
        print("\n[*] Restoring original data...")
        
        backup_file = self.backup_dir / f"backup_{self.session_timestamp}.dat"
        metadata_file = self.backup_dir / f"metadata_{self.session_timestamp}.json"
        
        # Fallback: cerca il backup più recente se non troviamo quello di sessione
        if not backup_file.exists() or not metadata_file.exists():
            print(f"[!] Session backup not found, searching for most recent...")
            backup_files = sorted(self.backup_dir.glob("backup_*.dat"))
            metadata_files = sorted(self.backup_dir.glob("metadata_*.json"))
            
            if not backup_files or not metadata_files:
                print("[!] No backup files found")
                return False
            
            backup_file = backup_files[-1]
            metadata_file = metadata_files[-1]
            print(f"[*] Using backup: {backup_file.name}")
        
        try:
            # Carica metadata
            with open(metadata_file, 'r') as f:
                metadata = json.load(f)
            
            if 'backup_file_hash' in metadata:
                print("[*] Verifying backup file integrity...")
                current_hash = self._calculate_file_hash(backup_file)
                if current_hash != metadata['backup_file_hash']:
                    print("[!] CRITICAL: Backup file is corrupted!")
                    print(f"    Expected: {metadata['backup_file_hash'][:16]}...")
                    print(f"    Got:      {current_hash[:16]}...")
                    print("[!] Cannot safely restore. Manual intervention required.")
                    return False
                print("[+] Backup file integrity verified")
            
            # Verifica device identity
            if 'device_id' in metadata and self.device_id:
                if metadata['device_id'] != self.device_id:
                    print("[!] WARNING: Device identity mismatch!")
                    print(f"    Backup was for device ID: {metadata['device_id']}")
                    print(f"    Current device ID: {self.device_id}")
                    print("[!] The SD card may have been swapped!")
                    response = input("[?] Continue anyway? (yes/no): ")
                    if response.lower() != 'yes':
                        print("[!] Restore aborted by user")
                        return False
            
            # Restore data
            with open(self.device_path, 'r+b') as dev, open(backup_file, 'rb') as backup:
                sectors_items = list(metadata['sectors'].items())
                
                if TQDM_AVAILABLE:
                    iterator = tqdm(sectors_items, desc="Restoring", unit="sector",
                                  ncols=80, bar_format='{l_bar}{bar}| {n_fmt}/{total_fmt} [{elapsed}<{remaining}]')
                else:
                    iterator = sectors_items
                
                for sector_str, info in iterator:
                    sector_num = int(sector_str)
                    
                    # Leggi dal backup
                    backup.seek(info['offset_in_backup'])
                    original_data = backup.read(SECTOR_SIZE)
                    
                    # Scrivi sul device
                    offset = sector_num * SECTOR_SIZE
                    dev.seek(offset)
                    dev.write(original_data)
                    dev.flush()
                
                os.fsync(dev.fileno())
            
            # Verifica restore
            print("[*] Verifying restore...")
            errors = 0
            with open(self.device_path, 'rb') as dev, open(backup_file, 'rb') as backup:
                if TQDM_AVAILABLE:
                    verify_iterator = tqdm(sectors_items, desc="Verifying", unit="sector",
                                         ncols=80, bar_format='{l_bar}{bar}| {n_fmt}/{total_fmt} [{elapsed}<{remaining}]')
                else:
                    verify_iterator = sectors_items
                
                for sector_str, info in verify_iterator:
                    sector_num = int(sector_str)
                    
                    # Leggi originale dal backup
                    backup.seek(info['offset_in_backup'])
                    original_data = backup.read(SECTOR_SIZE)
                    original_hash = hashlib.sha256(original_data).hexdigest()
                    
                    # Leggi dal device
                    offset = sector_num * SECTOR_SIZE
                    dev.seek(offset)
                    restored_data = dev.read(SECTOR_SIZE)
                    restored_hash = hashlib.sha256(restored_data).hexdigest()
                    
                    if original_hash != restored_hash:
                        errors += 1
                        print(f"[!] Verification failed for sector {sector_num}")
            
            if errors == 0:
                print(f"[+] All sectors restored successfully")
                return True
            else:
                print(f"[!] {errors} sectors failed verification")
                return False
                
        except Exception as e:
            print(f"[!] Restore failed: {e}")
            return False
    
    # Cleanup selettivo
    def cleanup_backup(self):
        """Remove only this session's backup files"""
        print("[*] Cleaning up backup files...")
        
        # Rimuovi solo i file di questa sessione
        session_files = [
            self.backup_dir / f"backup_{self.session_timestamp}.dat",
            self.backup_dir / f"metadata_{self.session_timestamp}.json"
        ]
        
        removed = 0
        for f in session_files:
            if f.exists():
                f.unlink()
                removed += 1
        
        print(f"[+] Cleanup completed ({removed} files removed)")
        
        # Avvisa se ci sono altri file nella directory
        remaining = list(self.backup_dir.glob("*"))
        if remaining:
            print(f"[*] Note: {len(remaining)} other file(s) remain in backup directory")
    
    def generate_report(self, analysis: Dict) -> str:
        """Generate final report"""
        report = []
        report.append("=" * 60)
        report.append("SD CARD HEALTH TEST REPORT")
        report.append("=" * 60)
        report.append(f"Device: {self.device_path}")
        report.append(f"Device ID: {self.device_id}")
        report.append(f"Test Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        report.append(f"Total Sectors: {self.results['total_sectors']}")
        report.append(f"Tested Sectors: {self.results['tested_sectors']}")
        report.append("")
        report.append("HEALTH SCORE")
        report.append("-" * 60)
        report.append(f"Score: {self.results['health_score']:.1f}/100 ({self.results['status']})")
        report.append("")
        
        if 'read_latency' in analysis:
            report.append("PERFORMANCE")
            report.append("-" * 60)
            report.append(f"Read Latency (mean): {analysis['read_latency']['mean']*1000:.2f} ms")
            report.append(f"Read Latency (p95): {analysis['read_latency']['p95']*1000:.2f} ms")
            report.append(f"Write Latency (mean): {analysis['write_latency']['mean']*1000:.2f} ms")
            report.append("")
        
        if 'error_rates' in analysis:
            report.append("ERROR RATES")
            report.append("-" * 60)
            report.append(f"Bit Error Rate: {analysis['error_rates']['bit_error_rate']:.2e}")
            report.append(f"Verify Error Rate: {analysis['error_rates']['verify_error_rate']:.2%}")
            report.append("")
        
        if self.results['errors']:
            report.append("ERRORS DETECTED")
            report.append("-" * 60)
            for error in self.results['errors'][:10]:  # First 10
                report.append(f"  Sector {error['sector']}: {error['type']} ({error.get('count', 'N/A')} bits)")
            if len(self.results['errors']) > 10:
                report.append(f"  ... and {len(self.results['errors']) - 10} more")
            report.append("")
        
        report.append("RECOMMENDATIONS")
        report.append("-" * 60)
        score = self.results['health_score']
        if score >= 90:
            report.append("  Card is in excellent condition. No immediate action needed.")
        elif score >= 75:
            report.append("  Card is in good condition. Monitor periodically.")
        elif score >= 50:
            report.append("  Card shows signs of wear. Consider backup more frequently.")
        elif score >= 25:
            report.append("  Card is degrading. Backup important data and plan replacement.")
        else:
            report.append("  Card is in critical condition. Replace immediately and backup data.")
        
        report.append("=" * 60)
        
        return "\n".join(report)
    
    def run_full_test(self, num_sectors: int = MIN_TEST_SECTORS, 
                     keep_backup: bool = False) -> bool:
        """Run complete test cycle"""
        self.results['start_time'] = datetime.now().isoformat()
        
        # Initialize
        if not self.initialize():
            return False
        
        # Select sectors
        if not self.select_test_sectors(num_sectors):
            print("[!] Failed to select test sectors")
            return False
        
        # Backup
        if not self.backup_sectors():
            return False
        
        # Installa signal handler per CTRL+C dopo il backup
        self._install_signal_handler()
        
        try:
            # Run tests
            test_results = self.run_basic_test()
            
            # Se interrotto, salta analisi e report
            if self._interrupted:
                print("\n[!] Test was interrupted - skipping analysis")
            else:
                analysis = self.run_statistical_analysis(test_results)
                
                # Calculate score
                score, status = self.calculate_health_score(test_results, analysis)
                self.results['health_score'] = score
                self.results['status'] = status
                self.results['performance'] = analysis
                
                # Generate report
                print("\n" + self.generate_report(analysis))
                
                # Save report
                report_file = self.backup_dir / f"report_{self.session_timestamp}.txt"
                with open(report_file, 'w') as f:
                    f.write(self.generate_report(analysis))
                print(f"\n[+] Report saved: {report_file}")
            
        finally:
            # Ripristina signal handler originale
            self._restore_signal_handler()
            
            # Always attempt restore
            restore_success = self.restore_sectors()
            
            # Cleanup selettivo, solo se restore ok
            if restore_success and not keep_backup:
                self.cleanup_backup()
            elif not restore_success:
                print("\n" + "!"*60)
                print("CRITICAL: Restore failed! Backup files preserved.")
                print(f"Backup location: {self.backup_dir}")
                print("DO NOT delete these files - they contain your original data!")
                print("\nTo manually restore:")
                print(f"  python3 -c \"from sd_health_tester import SafeSDTester; ")
                print(f"  t = SafeSDTester('{self.device_path}', '{self.backup_dir}'); ")
                print(f"  t.session_timestamp = '{self.session_timestamp}'; ")
                print(f"  t.initialize(); ")
                print(f"  t.restore_sectors()\"")
                print("\nPossible causes:")
                print("  - SD card hardware failure")
                print("  - Card reader disconnected")
                print("  - Damaged sectors")
                print("!"*60)
        
        self.results['end_time'] = datetime.now().isoformat()
        return True


def main():
    parser = argparse.ArgumentParser(
        description='SafeSDTester - Test SD card health without losing data',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  sudo python3 sd_health_tester.py /dev/sdb
  sudo python3 sd_health_tester.py /dev/mmcblk0 --sectors 2000
  sudo python3 sd_health_tester.py /dev/sdc --keep-backup
        """
    )
    
    parser.add_argument('device', help='Device path (e.g., /dev/sdb, /dev/mmcblk0)')
    parser.add_argument('--sectors', type=int, default=MIN_TEST_SECTORS,
                       help=f'Number of sectors to test (default: {MIN_TEST_SECTORS})')
    parser.add_argument('--keep-backup', action='store_true',
                       help='Keep backup files after test')
    parser.add_argument('--backup-dir', default=BACKUP_DIR,
                       help=f'Backup directory (default: {BACKUP_DIR})')
    
    args = parser.parse_args()
    
    # Check root
    if os.geteuid() != 0:
        print("[!] This tool requires root privileges")
        print("[!] Please run with sudo")
        sys.exit(1)
    
    # Check device
    if not os.path.exists(args.device):
        print(f"[!] Device not found: {args.device}")
        sys.exit(1)
    
    # Warning
    print("\n" + "="*60)
    print("WARNING: This tool will write to the device")
    print("Original data will be backed up and restored")
    print(f"Device: {args.device}")
    print("="*60)
    response = input("\nContinue? (yes/no): ")
    
    if response.lower() != 'yes':
        print("Aborted.")
        sys.exit(0)
    
    # Run test
    tester = SafeSDTester(args.device, args.backup_dir)
    success = tester.run_full_test(args.sectors, args.keep_backup)
    
    sys.exit(0 if success else 1)


if __name__ == '__main__':
    main()
