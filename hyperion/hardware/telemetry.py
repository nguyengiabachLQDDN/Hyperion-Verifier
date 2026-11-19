"""Cross-platform and Win32 ctypes hardware telemetry and safety circuit-breaker."""

from dataclasses import dataclass, asdict
import ctypes
from ctypes import wintypes
import os
import platform
import time
import tracemalloc
from typing import Dict, Any, Optional, Tuple

from hyperion.config import SafetyConfig


BELOW_NORMAL_PRIORITY_CLASS = 0x00004000


if os.name == "nt":
    class MEMORYSTATUSEX(ctypes.Structure):
        _fields_ = [
            ("dwLength", wintypes.DWORD),
            ("dwMemoryLoad", wintypes.DWORD),
            ("ullTotalPhys", ctypes.c_uint64),
            ("ullAvailPhys", ctypes.c_uint64),
            ("ullTotalPageFile", ctypes.c_uint64),
            ("ullAvailPageFile", ctypes.c_uint64),
            ("ullTotalVirtual", ctypes.c_uint64),
            ("ullAvailVirtual", ctypes.c_uint64),
            ("sullAvailExtendedVirtual", ctypes.c_uint64),
        ]

    class PROCESS_MEMORY_COUNTERS_EX(ctypes.Structure):
        _fields_ = [
            ("cb", wintypes.DWORD),
            ("PageFaultCount", wintypes.DWORD),
            ("PeakWorkingSetSize", ctypes.c_size_t),
            ("WorkingSetSize", ctypes.c_size_t),
            ("QuotaPeakPagedPoolUsage", ctypes.c_size_t),
            ("QuotaPagedPoolUsage", ctypes.c_size_t),
            ("QuotaPeakNonPagedPoolUsage", ctypes.c_size_t),
            ("QuotaNonPagedPoolUsage", ctypes.c_size_t),
            ("PagefileUsage", ctypes.c_size_t),
            ("PeakPagefileUsage", ctypes.c_size_t),
            ("PrivateUsage", ctypes.c_size_t),
        ]

    class FILETIME(ctypes.Structure):
        _fields_ = [
            ("dwLowDateTime", wintypes.DWORD),
            ("dwHighDateTime", wintypes.DWORD),
        ]

    def _filetime_to_int(ft: FILETIME) -> int:
        return (ft.dwHighDateTime << 32) | ft.dwLowDateTime


_kernel32: Optional[Any] = None
_psapi: Optional[Any] = None

if os.name == "nt":
    _kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
    _psapi = ctypes.WinDLL("psapi", use_last_error=True)

    _kernel32.GetCurrentProcess.argtypes = []
    _kernel32.GetCurrentProcess.restype = wintypes.HANDLE

    _kernel32.SetPriorityClass.argtypes = [wintypes.HANDLE, wintypes.DWORD]
    _kernel32.SetPriorityClass.restype = wintypes.BOOL

    _kernel32.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
    _kernel32.OpenProcess.restype = wintypes.HANDLE

    _kernel32.CloseHandle.argtypes = [wintypes.HANDLE]
    _kernel32.CloseHandle.restype = wintypes.BOOL

    _psapi.GetProcessMemoryInfo.argtypes = [
        wintypes.HANDLE,
        ctypes.POINTER(PROCESS_MEMORY_COUNTERS_EX),
        wintypes.DWORD,
    ]
    _psapi.GetProcessMemoryInfo.restype = wintypes.BOOL

    _kernel32.GlobalMemoryStatusEx.argtypes = [ctypes.POINTER(MEMORYSTATUSEX)]
    _kernel32.GlobalMemoryStatusEx.restype = wintypes.BOOL

    _kernel32.GetSystemTimes.argtypes = [
        ctypes.POINTER(FILETIME),
        ctypes.POINTER(FILETIME),
        ctypes.POINTER(FILETIME),
    ]
    _kernel32.GetSystemTimes.restype = wintypes.BOOL


def get_win32_bindings() -> Dict[str, Any]:
    """Return cached Win32 DLL bindings (or None values on non-Windows hosts)."""
    return {"kernel32": _kernel32, "psapi": _psapi}


def set_worker_low_priority() -> bool:
    """Lower current process priority on Windows so interactive UI never freezes."""
    if os.name == "nt" and _kernel32 is not None:
        try:
            handle = _kernel32.GetCurrentProcess()
            res = _kernel32.SetPriorityClass(handle, BELOW_NORMAL_PRIORITY_CLASS)
            return bool(res)
        except Exception:
            return False
    else:
        try:
            os.nice(5)
            return True
        except Exception:
            return False


def get_machine_profile() -> Dict[str, Any]:
    """Collect static CPU and physical memory profile for cross-machine benchmarking."""
    cpu_name = platform.processor() or platform.machine() or "CPU không xác định"
    if os.name == "nt":
        try:
            import winreg
            key = winreg.OpenKey(
                winreg.HKEY_LOCAL_MACHINE,
                r"HARDWARE\DESCRIPTION\System\CentralProcessor\0",
            )
            val, _ = winreg.QueryValueEx(key, "ProcessorNameString")
            if val:
                cpu_name = str(val).strip()
            winreg.CloseKey(key)
        except Exception:
            pass

    total_ram_gb = 0.0
    if os.name == "nt" and _kernel32 is not None:
        try:
            stat = MEMORYSTATUSEX()
            stat.dwLength = ctypes.sizeof(MEMORYSTATUSEX)
            if _kernel32.GlobalMemoryStatusEx(ctypes.byref(stat)):
                total_ram_gb = round(stat.ullTotalPhys / (1024 ** 3), 2)
        except Exception:
            pass

    return {
        "hostname": platform.node() or "máy-không-xác-định",
        "os": f"{platform.system()} {platform.release()}",
        "arch": platform.machine(),
        "cpu_model": cpu_name,
        "logical_cores": os.cpu_count() or 1,
        "total_ram_gb": total_ram_gb,
        "python_version": platform.python_version(),
    }


@dataclass
class HardwareSnapshot:
    timestamp: float
    cpu_load_pct: float
    total_ram_mb: float
    avail_ram_mb: float
    free_ram_pct: float
    system_ram_load_pct: float
    process_ram_mb: float
    tracemalloc_mb: float
    logical_cores: int

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)


class HardwareMonitor:
    """Tracks real-time system CPU, physical memory, and process working set."""

    def __init__(self) -> None:
        self._prev_idle: Optional[int] = None
        self._prev_kernel: Optional[int] = None
        self._prev_user: Optional[int] = None
        if not tracemalloc.is_tracing():
            tracemalloc.start()
        self._prime_cpu_counters()

    def _prime_cpu_counters(self) -> None:
        if os.name == "nt" and _kernel32 is not None:
            idle, kernel, user = FILETIME(), FILETIME(), FILETIME()
            try:
                if _kernel32.GetSystemTimes(
                    ctypes.byref(idle), ctypes.byref(kernel), ctypes.byref(user)
                ):
                    self._prev_idle = _filetime_to_int(idle)
                    self._prev_kernel = _filetime_to_int(kernel)
                    self._prev_user = _filetime_to_int(user)
            except Exception:
                pass

    def _sample_cpu_pct(self) -> float:
        if os.name == "nt" and _kernel32 is not None:
            idle, kernel, user = FILETIME(), FILETIME(), FILETIME()
            try:
                ok = _kernel32.GetSystemTimes(
                    ctypes.byref(idle), ctypes.byref(kernel), ctypes.byref(user)
                )
                if not ok:
                    return 0.0
                cur_idle = _filetime_to_int(idle)
                cur_kernel = _filetime_to_int(kernel)
                cur_user = _filetime_to_int(user)

                if self._prev_idle is None:
                    self._prev_idle, self._prev_kernel, self._prev_user = cur_idle, cur_kernel, cur_user
                    return 0.0

                d_idle = cur_idle - self._prev_idle
                d_kernel = cur_kernel - self._prev_kernel
                d_user = cur_user - self._prev_user
                self._prev_idle, self._prev_kernel, self._prev_user = cur_idle, cur_kernel, cur_user

                total = d_kernel + d_user
                if total <= 0:
                    return 0.0
                busy = max(0, total - d_idle)
                return round(min(100.0, max(0.0, (busy / total) * 100.0)), 1)
            except Exception:
                return 0.0
        else:
            try:
                load1, _, _ = os.getloadavg()
                cores = os.cpu_count() or 1
                return round(min(100.0, (load1 / cores) * 100.0), 1)
            except Exception:
                return 0.0

    def _sample_memory(self) -> Tuple[float, float, float, float]:
        """Returns (total_mb, avail_mb, free_pct, sys_load_pct)."""
        if os.name == "nt" and _kernel32 is not None:
            try:
                stat = MEMORYSTATUSEX()
                stat.dwLength = ctypes.sizeof(MEMORYSTATUSEX)
                if _kernel32.GlobalMemoryStatusEx(ctypes.byref(stat)):
                    total_mb = stat.ullTotalPhys / (1024 * 1024)
                    avail_mb = stat.ullAvailPhys / (1024 * 1024)
                    free_pct = (avail_mb / total_mb * 100.0) if total_mb > 0 else 50.0
                    return (
                        round(total_mb, 1),
                        round(avail_mb, 1),
                        round(free_pct, 1),
                        float(stat.dwMemoryLoad),
                    )
            except Exception:
                pass
        return (8192.0, 4096.0, 50.0, 50.0)

    def _sample_pid_ram_mb(self, pid: int, psapi: Any, kernel32: Any) -> float:
        PROCESS_QUERY_LIMITED_INFORMATION = 0x1000
        PROCESS_VM_READ = 0x0010
        handle = kernel32.OpenProcess(
            PROCESS_QUERY_LIMITED_INFORMATION | PROCESS_VM_READ, False, int(pid)
        )
        if not handle:
            return 0.0
        try:
            counters = PROCESS_MEMORY_COUNTERS_EX()
            counters.cb = ctypes.sizeof(PROCESS_MEMORY_COUNTERS_EX)
            if psapi.GetProcessMemoryInfo(handle, ctypes.byref(counters), counters.cb):
                return counters.WorkingSetSize / (1024 * 1024)
            return 0.0
        finally:
            kernel32.CloseHandle(handle)

    def _sample_process_ram_mb(self, child_pids: Optional[Tuple[int, ...]] = None) -> float:
        if os.name == "nt" and _kernel32 is not None and _psapi is not None:
            try:
                counters = PROCESS_MEMORY_COUNTERS_EX()
                counters.cb = ctypes.sizeof(PROCESS_MEMORY_COUNTERS_EX)
                handle = _kernel32.GetCurrentProcess()
                total_mb = 0.0
                if _psapi.GetProcessMemoryInfo(handle, ctypes.byref(counters), counters.cb):
                    total_mb += counters.WorkingSetSize / (1024 * 1024)

                if child_pids:
                    cur_pid = os.getpid()
                    for cpid in set(child_pids):
                        if cpid and cpid != cur_pid:
                            total_mb += self._sample_pid_ram_mb(cpid, _psapi, _kernel32)
                return round(total_mb, 1)
            except Exception:
                pass
        return 0.0

    def snapshot(
        self,
        extra_worker_ram_mb: float = 0.0,
        child_pids: Optional[Tuple[int, ...]] = None,
    ) -> HardwareSnapshot:
        cpu_pct = self._sample_cpu_pct()
        total_mb, avail_mb, free_pct, load_pct = self._sample_memory()
        proc_mb = self._sample_process_ram_mb(child_pids=child_pids) + extra_worker_ram_mb
        tm_cur, _ = tracemalloc.get_traced_memory() if tracemalloc.is_tracing() else (0, 0)
        tm_mb = round(tm_cur / (1024 * 1024), 2)
        if proc_mb <= 0.0:
            proc_mb = tm_mb
        return HardwareSnapshot(
            timestamp=time.time(),
            cpu_load_pct=cpu_pct,
            total_ram_mb=total_mb,
            avail_ram_mb=avail_mb,
            free_ram_pct=free_pct,
            system_ram_load_pct=load_pct,
            process_ram_mb=round(proc_mb, 1),
            tracemalloc_mb=tm_mb,
            logical_cores=os.cpu_count() or 1,
        )


class SafetyGovernor:
    """Enforces RAM ceilings, free-RAM floors, and time limits with zero disk thrashing."""

    def __init__(self, config: SafetyConfig, monitor: Optional[HardwareMonitor] = None) -> None:
        self.config = config
        self.monitor = monitor or HardwareMonitor()
        self.start_time = time.monotonic()
        self.tripped = False
        self.trip_reason = ""

    def reset_timer(self) -> None:
        self.start_time = time.monotonic()
        self.tripped = False
        self.trip_reason = ""

    def check_health(
        self,
        extra_worker_ram_mb: float = 0.0,
        child_pids: Optional[Tuple[int, ...]] = None,
    ) -> Tuple[bool, str, HardwareSnapshot]:
        snap = self.monitor.snapshot(
            extra_worker_ram_mb=extra_worker_ram_mb,
            child_pids=child_pids,
        )
        elapsed = time.monotonic() - self.start_time

        if elapsed > self.config.max_duration_sec:
            self.tripped = True
            self.trip_reason = (
                f"Đã đạt giới hạn thời gian chạy ({elapsed:.1f}s > {self.config.max_duration_sec}s)"
            )
            return False, self.trip_reason, snap

        if snap.free_ram_pct < self.config.min_free_system_ram_pct:
            self.tripped = True
            self.trip_reason = (
                f"Ngưỡng RAM trống hệ thống bị vi phạm ({snap.free_ram_pct:.1f}% < "
                f"{self.config.min_free_system_ram_pct:.1f}%)"
            )
            return False, self.trip_reason, snap

        if snap.process_ram_mb > self.config.max_process_ram_mb:
            self.tripped = True
            self.trip_reason = (
                f"Vượt trần RAM tiến trình ({snap.process_ram_mb:.1f} MB > "
                f"{self.config.max_process_ram_mb} MB)"
            )
            return False, self.trip_reason, snap

        return True, "OK", snap
