#!/usr/bin/env python3
"""
AC Holdings GBA Emulator v1.0
(C) A.C Holdings / Team Flames 1999-2026

A real Game Boy Advance emulator featuring:
- ARM7TDMI CPU (ARM + THUMB instruction sets)
- Correct GBA memory map (BIOS, EWRAM, IWRAM, IO, PAL, VRAM, OAM, ROM)
- PPU with Mode 0-5 support, background & sprite rendering
- DMA controller (4 channels)
- Timer support (4 timers)
- Keypad input
- HLE BIOS (SWI calls)
- Tkinter GUI at native 240x160, scaled 2x

Single self-contained file. No external assets.
Requires: Python 3.8+, tkinter, Pillow (pip install Pillow)
"""

import tkinter as tk
from tkinter import filedialog, messagebox
import struct
import os
import sys
import time
import array
import threading

try:
    from PIL import Image, ImageTk
except ImportError:
    print("Pillow required: pip install Pillow --break-system-packages")
    sys.exit(1)

# =============================================================================
# CONSTANTS
# =============================================================================

CLOCK_SPEED = 16_777_216  # 16.78 MHz
CYCLES_PER_FRAME = 280896  # 228 scanlines * 1232 dots
SCREEN_W, SCREEN_H = 240, 160
SCALE = 2

# Memory regions
BIOS_START = 0x00000000; BIOS_SIZE = 0x4000
EWRAM_START = 0x02000000; EWRAM_SIZE = 0x40000
IWRAM_START = 0x03000000; IWRAM_SIZE = 0x8000
IO_START = 0x04000000; IO_SIZE = 0x400
PAL_START = 0x05000000; PAL_SIZE = 0x400
VRAM_START = 0x06000000; VRAM_SIZE = 0x18000
OAM_START = 0x07000000; OAM_SIZE = 0x400
ROM_START = 0x08000000; ROM_MAX = 0x02000000
SRAM_START = 0x0E000000; SRAM_SIZE = 0x10000

# IO Registers
REG_DISPCNT   = 0x000
REG_DISPSTAT  = 0x004
REG_VCOUNT    = 0x006
REG_BG0CNT    = 0x008
REG_BG1CNT    = 0x00A
REG_BG2CNT    = 0x00C
REG_BG3CNT    = 0x00E
REG_BG0HOFS   = 0x010
REG_BG0VOFS   = 0x012
REG_BG1HOFS   = 0x014
REG_BG1VOFS   = 0x016
REG_BG2HOFS   = 0x018
REG_BG2VOFS   = 0x01A
REG_BG3HOFS   = 0x01C
REG_BG3VOFS   = 0x01E
REG_BG2PA     = 0x020
REG_BG2PB     = 0x022
REG_BG2PC     = 0x024
REG_BG2PD     = 0x026
REG_BG2X      = 0x028
REG_BG2Y      = 0x02C
REG_BG3PA     = 0x030
REG_BG3PB     = 0x032
REG_BG3PC     = 0x034
REG_BG3PD     = 0x036
REG_BG3X      = 0x038
REG_BG3Y      = 0x03C
REG_WIN0H     = 0x040
REG_WIN1H     = 0x042
REG_WIN0V     = 0x044
REG_WIN1V     = 0x046
REG_WININ     = 0x048
REG_WINOUT    = 0x04A
REG_BLDCNT    = 0x050
REG_BLDALPHA  = 0x052
REG_BLDY      = 0x054
REG_TM0CNT_L  = 0x100
REG_TM0CNT_H  = 0x102
REG_TM1CNT_L  = 0x104
REG_TM1CNT_H  = 0x106
REG_TM2CNT_L  = 0x108
REG_TM2CNT_H  = 0x10A
REG_TM3CNT_L  = 0x10C
REG_TM3CNT_H  = 0x10E
REG_KEYINPUT  = 0x130
REG_KEYCNT    = 0x132
REG_IE        = 0x200
REG_IF        = 0x202
REG_WAITCNT   = 0x204
REG_IME       = 0x208
REG_HALTCNT   = 0x300

# DMA registers base
REG_DMA0SAD   = 0x0B0
REG_DMA0DAD   = 0x0B4
REG_DMA0CNT_L = 0x0B8
REG_DMA0CNT_H = 0x0BA

# IRQ bits
IRQ_VBLANK  = 0x0001
IRQ_HBLANK  = 0x0002
IRQ_VCOUNT  = 0x0004
IRQ_TIMER0  = 0x0008
IRQ_TIMER1  = 0x0010
IRQ_TIMER2  = 0x0020
IRQ_TIMER3  = 0x0040
IRQ_DMA0    = 0x0100
IRQ_DMA1    = 0x0200
IRQ_DMA2    = 0x0400
IRQ_DMA3    = 0x0800
IRQ_KEYPAD  = 0x1000

# Key bits (active low in KEYINPUT)
KEY_A      = 0x001
KEY_B      = 0x002
KEY_SELECT = 0x004
KEY_START  = 0x008
KEY_RIGHT  = 0x010
KEY_LEFT   = 0x020
KEY_UP     = 0x040
KEY_DOWN   = 0x080
KEY_R      = 0x100
KEY_L      = 0x200

# CPU modes
MODE_USR = 0x10
MODE_FIQ = 0x11
MODE_IRQ = 0x12
MODE_SVC = 0x13
MODE_ABT = 0x17
MODE_UND = 0x1B
MODE_SYS = 0x1F

# CPSR flags
FLAG_N = 0x80000000
FLAG_Z = 0x40000000
FLAG_C = 0x20000000
FLAG_V = 0x10000000
FLAG_I = 0x00000080
FLAG_F = 0x00000040
FLAG_T = 0x00000020

MASK32 = 0xFFFFFFFF

# =============================================================================
# HLE BIOS - minimal software interrupt handlers
# =============================================================================

class HleBios:
    """High-Level Emulation of GBA BIOS SWI calls."""
    
    @staticmethod
    def handle_swi(cpu, comment):
        fn = comment
        if fn == 0x00:  # SoftReset
            cpu.regs[15] = 0x08000000
            cpu.cpsr = MODE_SYS
        elif fn == 0x01:  # RegisterRamReset
            pass  # stub
        elif fn == 0x02:  # Halt
            cpu.halted = True
        elif fn == 0x04:  # IntrWait
            cpu.halted = True
        elif fn == 0x05:  # VBlankIntrWait
            cpu.halted = True
            cpu.waiting_vblank = True
        elif fn == 0x06:  # Div
            num = cpu.s32(cpu.regs[0])
            den = cpu.s32(cpu.regs[1])
            if den == 0:
                return
            cpu.regs[0] = abs(num // den) if (num ^ den) >= 0 else -(abs(num) // abs(den))
            cpu.regs[0] &= MASK32
            cpu.regs[1] = abs(num) % abs(den)
            cpu.regs[3] = abs(cpu.s32(cpu.regs[0]))
        elif fn == 0x07:  # DivArm
            num = cpu.s32(cpu.regs[1])
            den = cpu.s32(cpu.regs[0])
            if den == 0:
                return
            cpu.regs[0] = abs(num // den) if (num ^ den) >= 0 else -(abs(num) // abs(den))
            cpu.regs[0] &= MASK32
            cpu.regs[1] = abs(num) % abs(den)
            cpu.regs[3] = abs(cpu.s32(cpu.regs[0]))
        elif fn == 0x08:  # Sqrt
            val = cpu.regs[0]
            cpu.regs[0] = int(val ** 0.5)
        elif fn == 0x09:  # ArcTan
            pass  # stub
        elif fn == 0x0A:  # ArcTan2
            pass  # stub
        elif fn == 0x0B:  # CpuSet
            HleBios._cpu_set(cpu)
        elif fn == 0x0C:  # CpuFastSet
            HleBios._cpu_fast_set(cpu)
        elif fn == 0x0E:  # BgAffineSet
            pass  # stub
        elif fn == 0x0F:  # ObjAffineSet
            pass  # stub
        elif fn == 0x10:  # BitUnPack
            pass
        elif fn == 0x11:  # LZ77UnCompWram
            HleBios._lz77_decomp(cpu, False)
        elif fn == 0x12:  # LZ77UnCompVram
            HleBios._lz77_decomp(cpu, True)
        elif fn == 0x13:  # HuffUnComp
            pass
        elif fn == 0x14:  # RLUnCompWram
            HleBios._rl_decomp(cpu)
        elif fn == 0x15:  # RLUnCompVram
            HleBios._rl_decomp(cpu)

    @staticmethod
    def _cpu_set(cpu):
        src = cpu.regs[0]
        dst = cpu.regs[1]
        cnt = cpu.regs[2]
        count = cnt & 0x1FFFFF
        fixed = (cnt >> 24) & 1
        size32 = (cnt >> 26) & 1
        mem = cpu.mem
        if size32:
            val = mem.read32(src)
            for i in range(count):
                mem.write32(dst + i * 4, val if fixed else mem.read32(src + i * 4))
        else:
            val = mem.read16(src)
            for i in range(count):
                mem.write16(dst + i * 2, val if fixed else mem.read16(src + i * 2))

    @staticmethod
    def _cpu_fast_set(cpu):
        src = cpu.regs[0]
        dst = cpu.regs[1]
        cnt = cpu.regs[2]
        count = cnt & 0x1FFFFF
        fixed = (cnt >> 24) & 1
        mem = cpu.mem
        val = mem.read32(src)
        for i in range(count):
            mem.write32(dst + i * 4, val if fixed else mem.read32(src + i * 4))

    @staticmethod
    def _lz77_decomp(cpu, vram):
        src = cpu.regs[0]
        dst = cpu.regs[1]
        mem = cpu.mem
        header = mem.read32(src)
        decomp_size = header >> 8
        src += 4
        out = 0
        while out < decomp_size:
            flags = mem.read8(src); src += 1
            for i in range(8):
                if out >= decomp_size:
                    break
                if flags & (0x80 >> i):
                    b1 = mem.read8(src); src += 1
                    b2 = mem.read8(src); src += 1
                    length = ((b1 >> 4) & 0xF) + 3
                    disp = ((b1 & 0xF) << 8) | b2
                    for j in range(length):
                        if out >= decomp_size:
                            break
                        val = mem.read8(dst + out - disp - 1)
                        mem.write8(dst + out, val)
                        out += 1
                else:
                    mem.write8(dst + out, mem.read8(src))
                    src += 1
                    out += 1

    @staticmethod
    def _rl_decomp(cpu):
        src = cpu.regs[0]
        dst = cpu.regs[1]
        mem = cpu.mem
        header = mem.read32(src)
        decomp_size = header >> 8
        src += 4
        out = 0
        while out < decomp_size:
            flag = mem.read8(src); src += 1
            if flag & 0x80:
                length = (flag & 0x7F) + 3
                val = mem.read8(src); src += 1
                for _ in range(length):
                    if out < decomp_size:
                        mem.write8(dst + out, val)
                        out += 1
            else:
                length = (flag & 0x7F) + 1
                for _ in range(length):
                    if out < decomp_size:
                        mem.write8(dst + out, mem.read8(src))
                        src += 1
                        out += 1


# =============================================================================
# MEMORY BUS
# =============================================================================

class MemoryBus:
    """GBA memory bus with correct address mapping."""

    def __init__(self):
        self.bios = bytearray(BIOS_SIZE)
        self.ewram = bytearray(EWRAM_SIZE)
        self.iwram = bytearray(IWRAM_SIZE)
        self.io = bytearray(IO_SIZE)
        self.palette = bytearray(PAL_SIZE)
        self.vram = bytearray(VRAM_SIZE)
        self.oam = bytearray(OAM_SIZE)
        self.rom = bytearray(0)
        self.sram = bytearray(SRAM_SIZE)
        
        # Callbacks for IO write side effects
        self.io_write_hook = None
        
        # Set default KEYINPUT to all released (all bits high)
        self._write_io16(REG_KEYINPUT, 0x03FF)
        
        # Install HLE BIOS 
        self._init_hle_bios()

    def _init_hle_bios(self):
        """Write minimal HLE BIOS vectors."""
        # IRQ handler at 0x18 -> branch to 0x128
        # We'll handle SWI in the CPU directly via HLE
        # Put IRQ vector
        struct.pack_into('<I', self.bios, 0x18, 0xEA000000 | (((0x128 - 0x18 - 8) >> 2) & 0xFFFFFF))
        # Put a simple IRQ handler at 0x128
        # In HLE mode the CPU catches IRQs before they reach BIOS
        pass

    def load_rom(self, data: bytes):
        self.rom = bytearray(data)

    def read8(self, addr: int) -> int:
        addr &= 0x0FFFFFFF
        region = addr >> 24
        if region == 0x00:
            return self.bios[addr & 0x3FFF]
        elif region == 0x02:
            return self.ewram[addr & 0x3FFFF]
        elif region == 0x03:
            return self.iwram[addr & 0x7FFF]
        elif region == 0x04:
            return self.io[addr & 0x3FF]
        elif region == 0x05:
            return self.palette[addr & 0x3FF]
        elif region == 0x06:
            a = addr & 0x1FFFF
            if a >= 0x18000:
                a -= 0x8000
            return self.vram[a]
        elif region == 0x07:
            return self.oam[addr & 0x3FF]
        elif 0x08 <= region <= 0x0D:
            off = addr - 0x08000000
            if off < len(self.rom):
                return self.rom[off]
            return 0
        elif region == 0x0E:
            return self.sram[addr & 0xFFFF]
        return 0

    def read16(self, addr: int) -> int:
        addr &= ~1
        a = addr & 0x0FFFFFFF
        region = a >> 24
        if region == 0x02:
            off = a & 0x3FFFF
            return self.ewram[off] | (self.ewram[off + 1] << 8)
        elif region == 0x03:
            off = a & 0x7FFF
            return self.iwram[off] | (self.iwram[off + 1] << 8)
        elif region == 0x04:
            off = a & 0x3FF
            if off + 1 < IO_SIZE:
                return self.io[off] | (self.io[off + 1] << 8)
            return 0
        elif region == 0x05:
            off = a & 0x3FF
            return self.palette[off] | (self.palette[off + 1] << 8)
        elif region == 0x06:
            off = a & 0x1FFFF
            if off >= 0x18000:
                off -= 0x8000
            return self.vram[off] | (self.vram[off + 1] << 8)
        elif region == 0x07:
            off = a & 0x3FF
            return self.oam[off] | (self.oam[off + 1] << 8)
        elif 0x08 <= region <= 0x0D:
            off = a - 0x08000000
            if off + 1 < len(self.rom):
                return self.rom[off] | (self.rom[off + 1] << 8)
            return 0
        elif region == 0x00:
            off = a & 0x3FFF
            return self.bios[off] | (self.bios[off + 1] << 8)
        return 0

    def read32(self, addr: int) -> int:
        addr &= ~3
        a = addr & 0x0FFFFFFF
        region = a >> 24
        if region == 0x02:
            off = a & 0x3FFFF
            return struct.unpack_from('<I', self.ewram, off)[0]
        elif region == 0x03:
            off = a & 0x7FFF
            return struct.unpack_from('<I', self.iwram, off)[0]
        elif region == 0x04:
            off = a & 0x3FF
            if off + 3 < IO_SIZE:
                return struct.unpack_from('<I', self.io, off)[0]
            return 0
        elif region == 0x05:
            off = a & 0x3FF
            return struct.unpack_from('<I', self.palette, off)[0]
        elif region == 0x06:
            off = a & 0x1FFFF
            if off >= 0x18000:
                off -= 0x8000
            return struct.unpack_from('<I', self.vram, off)[0]
        elif region == 0x07:
            off = a & 0x3FF
            return struct.unpack_from('<I', self.oam, off)[0]
        elif 0x08 <= region <= 0x0D:
            off = a - 0x08000000
            if off + 3 < len(self.rom):
                return struct.unpack_from('<I', self.rom, off)[0]
            return 0
        elif region == 0x00:
            off = a & 0x3FFF
            return struct.unpack_from('<I', self.bios, off)[0]
        elif region == 0x0E:
            return self.sram[a & 0xFFFF]
        return 0

    def write8(self, addr: int, val: int):
        val &= 0xFF
        addr &= 0x0FFFFFFF
        region = addr >> 24
        if region == 0x02:
            self.ewram[addr & 0x3FFFF] = val
        elif region == 0x03:
            self.iwram[addr & 0x7FFF] = val
        elif region == 0x04:
            off = addr & 0x3FF
            self.io[off] = val
            if self.io_write_hook:
                self.io_write_hook(off, val, 1)
        elif region == 0x05:
            # 8-bit writes to palette duplicate to 16-bit
            off = addr & 0x3FE
            self.palette[off] = val
            self.palette[off + 1] = val
        elif region == 0x06:
            # 8-bit writes to VRAM only work in bitmap modes
            a = addr & 0x1FFFF
            if a >= 0x18000:
                a -= 0x8000
            self.vram[a] = val
        elif region == 0x0E:
            self.sram[addr & 0xFFFF] = val

    def write16(self, addr: int, val: int):
        val &= 0xFFFF
        addr &= ~1
        a = addr & 0x0FFFFFFF
        region = a >> 24
        if region == 0x02:
            off = a & 0x3FFFF
            self.ewram[off] = val & 0xFF
            self.ewram[off + 1] = (val >> 8) & 0xFF
        elif region == 0x03:
            off = a & 0x7FFF
            self.iwram[off] = val & 0xFF
            self.iwram[off + 1] = (val >> 8) & 0xFF
        elif region == 0x04:
            off = a & 0x3FF
            self._write_io16(off, val)
            if self.io_write_hook:
                self.io_write_hook(off, val, 2)
        elif region == 0x05:
            off = a & 0x3FF
            self.palette[off] = val & 0xFF
            self.palette[off + 1] = (val >> 8) & 0xFF
        elif region == 0x06:
            off = a & 0x1FFFF
            if off >= 0x18000:
                off -= 0x8000
            self.vram[off] = val & 0xFF
            self.vram[off + 1] = (val >> 8) & 0xFF
        elif region == 0x07:
            off = a & 0x3FF
            self.oam[off] = val & 0xFF
            self.oam[off + 1] = (val >> 8) & 0xFF
        elif region == 0x0E:
            self.sram[a & 0xFFFF] = val & 0xFF

    def write32(self, addr: int, val: int):
        val &= MASK32
        addr &= ~3
        a = addr & 0x0FFFFFFF
        region = a >> 24
        if region == 0x02:
            off = a & 0x3FFFF
            struct.pack_into('<I', self.ewram, off, val)
        elif region == 0x03:
            off = a & 0x7FFF
            struct.pack_into('<I', self.iwram, off, val)
        elif region == 0x04:
            off = a & 0x3FF
            self._write_io16(off, val & 0xFFFF)
            self._write_io16(off + 2, (val >> 16) & 0xFFFF)
            if self.io_write_hook:
                self.io_write_hook(off, val, 4)
        elif region == 0x05:
            off = a & 0x3FF
            struct.pack_into('<I', self.palette, off, val)
        elif region == 0x06:
            off = a & 0x1FFFF
            if off >= 0x18000:
                off -= 0x8000
            struct.pack_into('<I', self.vram, off, val)
        elif region == 0x07:
            off = a & 0x3FF
            struct.pack_into('<I', self.oam, off, val)
        elif region == 0x0E:
            self.sram[a & 0xFFFF] = val & 0xFF

    def _write_io16(self, off: int, val: int):
        if off + 1 < IO_SIZE:
            self.io[off] = val & 0xFF
            self.io[off + 1] = (val >> 8) & 0xFF

    def read_io16(self, off: int) -> int:
        if off + 1 < IO_SIZE:
            return self.io[off] | (self.io[off + 1] << 8)
        return 0


# =============================================================================
# ARM7TDMI CPU
# =============================================================================

class ARM7TDMI:
    """ARM7TDMI CPU core with ARM and THUMB instruction sets."""

    def __init__(self, mem: MemoryBus):
        self.mem = mem
        self.regs = [0] * 16  # R0-R15
        self.cpsr = MODE_SYS  # Current Program Status Register
        
        # Banked registers per mode
        self.spsr = {MODE_FIQ: 0, MODE_IRQ: 0, MODE_SVC: 0, MODE_ABT: 0, MODE_UND: 0}
        self.banked_regs = {
            MODE_FIQ: [0] * 7,  # R8-R14
            MODE_IRQ: [0] * 2,  # R13-R14
            MODE_SVC: [0] * 2,
            MODE_ABT: [0] * 2,
            MODE_UND: [0] * 2,
        }
        
        self.halted = False
        self.waiting_vblank = False
        self.cycles = 0
        self.total_cycles = 0
        
        # Pipeline
        self.pipeline = [0, 0]
        self.pipeline_valid = False

        # Initial state
        self.regs[13] = 0x03007F00  # SP (IRQ)
        self.regs[15] = 0x08000000  # PC -> ROM entry
        self.cpsr = MODE_SYS

    @staticmethod
    def s32(v):
        return v - 0x100000000 if v & 0x80000000 else v

    @staticmethod
    def s8(v):
        return v - 0x100 if v & 0x80 else v

    @staticmethod
    def s16(v):
        return v - 0x10000 if v & 0x8000 else v

    def get_flag(self, f):
        return 1 if self.cpsr & f else 0

    def set_flag(self, f, val):
        if val:
            self.cpsr |= f
        else:
            self.cpsr &= ~f

    def in_thumb(self):
        return bool(self.cpsr & FLAG_T)

    def check_cond(self, cond):
        n = self.get_flag(FLAG_N)
        z = self.get_flag(FLAG_Z)
        c = self.get_flag(FLAG_C)
        v = self.get_flag(FLAG_V)
        if cond == 0x0: return z == 1       # EQ
        if cond == 0x1: return z == 0       # NE
        if cond == 0x2: return c == 1       # CS/HS
        if cond == 0x3: return c == 0       # CC/LO
        if cond == 0x4: return n == 1       # MI
        if cond == 0x5: return n == 0       # PL
        if cond == 0x6: return v == 1       # VS
        if cond == 0x7: return v == 0       # VC
        if cond == 0x8: return c == 1 and z == 0  # HI
        if cond == 0x9: return c == 0 or z == 1   # LS
        if cond == 0xA: return n == v       # GE
        if cond == 0xB: return n != v       # LT
        if cond == 0xC: return z == 0 and n == v   # GT
        if cond == 0xD: return z == 1 or n != v    # LE
        if cond == 0xE: return True          # AL
        return False  # NV / undefined

    def set_nz(self, result):
        self.set_flag(FLAG_N, result & 0x80000000)
        self.set_flag(FLAG_Z, result == 0)

    def _add_flags(self, a, b, result):
        self.set_nz(result & MASK32)
        self.set_flag(FLAG_C, result > MASK32)
        self.set_flag(FLAG_V, (~(a ^ b) & (a ^ result)) & 0x80000000)

    def _sub_flags(self, a, b, result):
        self.set_nz(result & MASK32)
        self.set_flag(FLAG_C, a >= b)
        self.set_flag(FLAG_V, ((a ^ b) & (a ^ result)) & 0x80000000)

    def fire_irq(self):
        """Enter IRQ mode."""
        if self.cpsr & FLAG_I:
            return
        old_cpsr = self.cpsr
        self.cpsr = (self.cpsr & ~0x1F) | MODE_IRQ | FLAG_I
        self.spsr[MODE_IRQ] = old_cpsr
        # Save return address
        if old_cpsr & FLAG_T:
            self.banked_regs[MODE_IRQ][1] = self.regs[14]
            self.banked_regs[MODE_IRQ][0] = self.regs[13]
            self.regs[14] = self.regs[15]  # Return address
            self.cpsr &= ~FLAG_T  # Switch to ARM mode
        else:
            self.banked_regs[MODE_IRQ][1] = self.regs[14]
            self.banked_regs[MODE_IRQ][0] = self.regs[13]
            self.regs[14] = self.regs[15] - 4
        self.regs[13] = 0x03007FA0  # IRQ stack
        self.regs[15] = 0x00000018  # IRQ vector
        # Use HLE: jump to GBA's IRQ handler in IWRAM
        irq_handler = self.mem.read32(0x03FFFFFC)
        if irq_handler:
            self.regs[15] = irq_handler
        self.pipeline_valid = False

    def step(self):
        """Execute one instruction."""
        if self.halted:
            self.cycles += 1
            return 1

        if self.in_thumb():
            return self._step_thumb()
        else:
            return self._step_arm()

    # =========================================================================
    # ARM INSTRUCTION EXECUTION
    # =========================================================================

    def _step_arm(self):
        pc = self.regs[15]
        instr = self.mem.read32(pc)
        self.regs[15] = (pc + 4) & MASK32
        cond = (instr >> 28) & 0xF

        if not self.check_cond(cond):
            self.regs[15] = (self.regs[15]) & MASK32
            self.cycles += 1
            return 1

        cycles = 1
        ident = (instr >> 20) & 0xFF
        bits74 = (instr >> 4) & 0xF

        # SWI
        if (instr & 0x0F000000) == 0x0F000000:
            comment = (instr >> 16) & 0xFF
            HleBios.handle_swi(self, comment)
            self.cycles += 3
            return 3

        # Branch / Branch with Link
        if (instr & 0x0E000000) == 0x0A000000:
            offset = instr & 0x00FFFFFF
            if offset & 0x800000:
                offset |= 0xFF000000
                offset -= 0x100000000
            target = (pc + 8 + offset * 4) & MASK32
            if instr & 0x01000000:  # BL
                self.regs[14] = (pc + 4) & MASK32
            self.regs[15] = target
            self.cycles += 3
            return 3

        # BX / BLX (register)
        if (instr & 0x0FFFFFF0) == 0x012FFF10:
            rn = instr & 0xF
            target = self.regs[rn]
            if target & 1:
                self.cpsr |= FLAG_T
                target &= ~1
            else:
                self.cpsr &= ~FLAG_T
            self.regs[15] = target & MASK32
            self.cycles += 3
            return 3
        
        # BLX register
        if (instr & 0x0FFFFFF0) == 0x012FFF30:
            rn = instr & 0xF
            self.regs[14] = (pc + 4) & MASK32
            target = self.regs[rn]
            if target & 1:
                self.cpsr |= FLAG_T
                target &= ~1
            else:
                self.cpsr &= ~FLAG_T
            self.regs[15] = target & MASK32
            self.cycles += 3
            return 3

        # Multiply
        if (instr & 0x0FC000F0) == 0x00000090:
            rd = (instr >> 16) & 0xF
            rn = (instr >> 12) & 0xF
            rs = (instr >> 8) & 0xF
            rm = instr & 0xF
            result = (self.regs[rm] * self.regs[rs]) & MASK32
            if instr & 0x00200000:  # MLA
                result = (result + self.regs[rn]) & MASK32
            self.regs[rd] = result
            if instr & 0x00100000:  # S
                self.set_nz(result)
            self.cycles += 3
            return 3

        # Multiply Long (UMULL, UMLAL, SMULL, SMLAL)
        if (instr & 0x0F8000F0) == 0x00800090:
            rd_hi = (instr >> 16) & 0xF
            rd_lo = (instr >> 12) & 0xF
            rs = (instr >> 8) & 0xF
            rm = instr & 0xF
            signed = bool(instr & 0x00400000)
            accumulate = bool(instr & 0x00200000)
            if signed:
                result = self.s32(self.regs[rm]) * self.s32(self.regs[rs])
            else:
                result = self.regs[rm] * self.regs[rs]
            if accumulate:
                result += (self.regs[rd_hi] << 32) | self.regs[rd_lo]
            result &= 0xFFFFFFFFFFFFFFFF
            self.regs[rd_lo] = result & MASK32
            self.regs[rd_hi] = (result >> 32) & MASK32
            if instr & 0x00100000:
                self.set_flag(FLAG_N, result & (1 << 63))
                self.set_flag(FLAG_Z, result == 0)
            self.cycles += 4
            return 4

        # Single Data Swap (SWP)
        if (instr & 0x0FB00FF0) == 0x01000090:
            rn = (instr >> 16) & 0xF
            rd = (instr >> 12) & 0xF
            rm = instr & 0xF
            addr = self.regs[rn]
            byte_swap = bool(instr & 0x00400000)
            if byte_swap:
                tmp = self.mem.read8(addr)
                self.mem.write8(addr, self.regs[rm] & 0xFF)
                self.regs[rd] = tmp
            else:
                tmp = self.mem.read32(addr)
                self.mem.write32(addr, self.regs[rm])
                self.regs[rd] = tmp
            self.cycles += 4
            return 4

        # Halfword / Signed transfers (LDRH, STRH, LDRSB, LDRSH)
        if (instr & 0x0E000090) == 0x00000090 and (bits74 & 0x9) == 0x9:
            op = (instr >> 5) & 0x3
            if op != 0:  # not multiply
                return self._arm_halfword_transfer(instr, pc)

        # MRS
        if (instr & 0x0FBF0FFF) == 0x010F0000:
            rd = (instr >> 12) & 0xF
            if instr & 0x00400000:  # SPSR
                mode = self.cpsr & 0x1F
                self.regs[rd] = self.spsr.get(mode, self.cpsr)
            else:
                self.regs[rd] = self.cpsr
            self.cycles += 1
            return 1

        # MSR
        if (instr & 0x0DB0F000) == 0x0120F000:
            return self._arm_msr(instr)

        # Data Processing
        if (instr & 0x0C000000) == 0x00000000:
            return self._arm_data_processing(instr, pc)

        # Single Data Transfer (LDR/STR)
        if (instr & 0x0C000000) == 0x04000000:
            return self._arm_single_transfer(instr, pc)

        # Block Data Transfer (LDM/STM)
        if (instr & 0x0E000000) == 0x08000000:
            return self._arm_block_transfer(instr, pc)

        # Coprocessor / Undefined
        self.cycles += 1
        return 1

    def _barrel_shift(self, instr, carry_in):
        """Compute shifted operand for ARM data processing."""
        if instr & 0x02000000:
            # Immediate
            imm = instr & 0xFF
            rot = ((instr >> 8) & 0xF) * 2
            if rot:
                val = ((imm >> rot) | (imm << (32 - rot))) & MASK32
                carry = (val >> 31) & 1
            else:
                val = imm
                carry = carry_in
            return val, carry
        else:
            rm = instr & 0xF
            val = self.regs[rm]
            if rm == 15:
                val = (val + 4) & MASK32  # PC+8 due to pipeline for register shifts
            shift_type = (instr >> 5) & 0x3
            if instr & 0x10:
                # Shift by register
                rs = (instr >> 8) & 0xF
                amount = self.regs[rs] & 0xFF
            else:
                amount = (instr >> 7) & 0x1F

            if amount == 0 and not (instr & 0x10):
                # Special cases for shift by 0
                if shift_type == 0:  # LSL #0
                    return val, carry_in
                elif shift_type == 1:  # LSR #0 means LSR #32
                    amount = 32
                elif shift_type == 2:  # ASR #0 means ASR #32
                    amount = 32
                elif shift_type == 3:  # ROR #0 means RRX
                    carry = val & 1
                    val = (carry_in << 31) | (val >> 1)
                    return val & MASK32, carry

            if amount == 0:
                return val, carry_in

            if shift_type == 0:  # LSL
                if amount < 32:
                    carry = (val >> (32 - amount)) & 1
                    val = (val << amount) & MASK32
                elif amount == 32:
                    carry = val & 1
                    val = 0
                else:
                    carry = 0
                    val = 0
            elif shift_type == 1:  # LSR
                if amount < 32:
                    carry = (val >> (amount - 1)) & 1
                    val = val >> amount
                elif amount == 32:
                    carry = (val >> 31) & 1
                    val = 0
                else:
                    carry = 0
                    val = 0
            elif shift_type == 2:  # ASR
                if amount >= 32:
                    if val & 0x80000000:
                        carry = 1
                        val = MASK32
                    else:
                        carry = 0
                        val = 0
                else:
                    carry = (val >> (amount - 1)) & 1
                    if val & 0x80000000:
                        val = (val >> amount) | (MASK32 << (32 - amount))
                        val &= MASK32
                    else:
                        val = val >> amount
            elif shift_type == 3:  # ROR
                amount &= 31
                if amount == 0:
                    return val, carry_in
                val = ((val >> amount) | (val << (32 - amount))) & MASK32
                carry = (val >> 31) & 1

            return val & MASK32, carry

    def _arm_data_processing(self, instr, pc):
        opcode = (instr >> 21) & 0xF
        s = bool(instr & 0x00100000)
        rn_idx = (instr >> 16) & 0xF
        rd = (instr >> 12) & 0xF
        
        carry_in = self.get_flag(FLAG_C)
        op2, shift_carry = self._barrel_shift(instr, carry_in)
        
        rn = self.regs[rn_idx]
        if rn_idx == 15:
            rn = (pc + 8) & MASK32
            
        result = 0
        write = True
        logical = False

        if opcode == 0x0:  # AND
            result = rn & op2; logical = True
        elif opcode == 0x1:  # EOR
            result = rn ^ op2; logical = True
        elif opcode == 0x2:  # SUB
            result = rn - op2
            if s: self._sub_flags(rn, op2, result)
            result &= MASK32
        elif opcode == 0x3:  # RSB
            result = op2 - rn
            if s: self._sub_flags(op2, rn, result)
            result &= MASK32
        elif opcode == 0x4:  # ADD
            result = rn + op2
            if s: self._add_flags(rn, op2, result)
            result &= MASK32
        elif opcode == 0x5:  # ADC
            result = rn + op2 + carry_in
            if s: self._add_flags(rn, op2 + carry_in, result)
            result &= MASK32
        elif opcode == 0x6:  # SBC
            result = rn - op2 - (1 - carry_in)
            if s: self._sub_flags(rn, op2 + (1 - carry_in), result)
            result &= MASK32
        elif opcode == 0x7:  # RSC
            result = op2 - rn - (1 - carry_in)
            if s: self._sub_flags(op2, rn + (1 - carry_in), result)
            result &= MASK32
        elif opcode == 0x8:  # TST
            result = rn & op2; logical = True; write = False
        elif opcode == 0x9:  # TEQ
            result = rn ^ op2; logical = True; write = False
        elif opcode == 0xA:  # CMP
            result = rn - op2
            self._sub_flags(rn, op2, result)
            result &= MASK32; write = False
        elif opcode == 0xB:  # CMN
            result = rn + op2
            self._add_flags(rn, op2, result)
            result &= MASK32; write = False
        elif opcode == 0xC:  # ORR
            result = rn | op2; logical = True
        elif opcode == 0xD:  # MOV
            result = op2; logical = True
        elif opcode == 0xE:  # BIC
            result = rn & ~op2; logical = True
        elif opcode == 0xF:  # MVN
            result = (~op2) & MASK32; logical = True

        if logical and s:
            self.set_nz(result & MASK32)
            self.set_flag(FLAG_C, shift_carry)

        if write:
            result &= MASK32
            self.regs[rd] = result
            if rd == 15:
                if s:
                    mode = self.cpsr & 0x1F
                    if mode in self.spsr:
                        self.cpsr = self.spsr[mode]
                self.pipeline_valid = False
                self.cycles += 3
                return 3

        self.cycles += 1
        return 1

    def _arm_single_transfer(self, instr, pc):
        rn_idx = (instr >> 16) & 0xF
        rd = (instr >> 12) & 0xF
        load = bool(instr & 0x00100000)
        writeback = bool(instr & 0x00200000)
        byte = bool(instr & 0x00400000)
        up = bool(instr & 0x00800000)
        pre = bool(instr & 0x01000000)
        imm = not bool(instr & 0x02000000)

        base = self.regs[rn_idx]
        if rn_idx == 15:
            base = (pc + 8) & MASK32

        if imm:
            offset = instr & 0xFFF
        else:
            rm = instr & 0xF
            shift_type = (instr >> 5) & 0x3
            shift_amount = (instr >> 7) & 0x1F
            offset = self.regs[rm]
            if shift_type == 0:
                offset = (offset << shift_amount) & MASK32
            elif shift_type == 1:
                offset = offset >> (shift_amount or 32)
            elif shift_type == 2:
                if shift_amount == 0: shift_amount = 32
                if offset & 0x80000000:
                    offset = (offset >> shift_amount) | (MASK32 << (32 - shift_amount))
                    offset &= MASK32
                else:
                    offset = offset >> shift_amount
            elif shift_type == 3:
                if shift_amount:
                    offset = ((offset >> shift_amount) | (offset << (32 - shift_amount))) & MASK32

        addr = (base + offset if up else base - offset) & MASK32 if pre else base

        cycles = 3
        if load:
            if byte:
                self.regs[rd] = self.mem.read8(addr)
            else:
                val = self.mem.read32(addr)
                # Unaligned rotation
                rot = (addr & 3) * 8
                if rot:
                    val = ((val >> rot) | (val << (32 - rot))) & MASK32
                self.regs[rd] = val
            if rd == 15:
                self.pipeline_valid = False
                cycles = 5
        else:
            val = self.regs[rd]
            if rd == 15:
                val = (pc + 12) & MASK32
            if byte:
                self.mem.write8(addr, val & 0xFF)
            else:
                self.mem.write32(addr, val)
            cycles = 2

        if not pre:
            addr = (base + offset if up else base - offset) & MASK32

        if writeback or not pre:
            if rn_idx != rd or not load:
                self.regs[rn_idx] = addr

        self.cycles += cycles
        return cycles

    def _arm_halfword_transfer(self, instr, pc):
        rn_idx = (instr >> 16) & 0xF
        rd = (instr >> 12) & 0xF
        load = bool(instr & 0x00100000)
        writeback = bool(instr & 0x00200000)
        up = bool(instr & 0x00800000)
        pre = bool(instr & 0x01000000)
        op = (instr >> 5) & 0x3

        base = self.regs[rn_idx]
        if rn_idx == 15:
            base = (pc + 8) & MASK32

        if instr & 0x00400000:  # Immediate offset
            offset = ((instr >> 4) & 0xF0) | (instr & 0xF)
        else:
            offset = self.regs[instr & 0xF]

        addr = (base + offset if up else base - offset) & MASK32 if pre else base

        cycles = 3
        if load:
            if op == 1:  # LDRH
                self.regs[rd] = self.mem.read16(addr)
            elif op == 2:  # LDRSB
                self.regs[rd] = self.s8(self.mem.read8(addr)) & MASK32
            elif op == 3:  # LDRSH
                self.regs[rd] = self.s16(self.mem.read16(addr)) & MASK32
            if rd == 15:
                self.pipeline_valid = False
                cycles = 5
        else:
            if op == 1:  # STRH
                self.mem.write16(addr, self.regs[rd] & 0xFFFF)
            cycles = 2

        if not pre:
            addr = (base + offset if up else base - offset) & MASK32

        if writeback or not pre:
            if rn_idx != rd or not load:
                self.regs[rn_idx] = addr

        self.cycles += cycles
        return cycles

    def _arm_block_transfer(self, instr, pc):
        rn_idx = (instr >> 16) & 0xF
        load = bool(instr & 0x00100000)
        writeback = bool(instr & 0x00200000)
        s_bit = bool(instr & 0x00400000)
        up = bool(instr & 0x00800000)
        pre = bool(instr & 0x01000000)
        reg_list = instr & 0xFFFF

        base = self.regs[rn_idx]
        count = bin(reg_list).count('1')
        
        if count == 0:
            self.cycles += 1
            return 1

        if up:
            addr = base
            if pre: addr += 4
        else:
            addr = base - count * 4
            if not pre: addr += 4
            else: addr = base - count * 4 + 4; addr -= 4

        # Simplified: sequential addressing
        if up:
            start = (base + 4) if pre else base
        else:
            start = (base - count * 4) if pre else (base - count * 4 + 4)

        offset = 0
        cycles = 2
        for i in range(16):
            if reg_list & (1 << i):
                a = (start + offset) & MASK32
                if load:
                    self.regs[i] = self.mem.read32(a)
                    if i == 15:
                        self.pipeline_valid = False
                        if s_bit and (self.cpsr & 0x1F) in self.spsr:
                            self.cpsr = self.spsr[self.cpsr & 0x1F]
                else:
                    val = self.regs[i]
                    if i == 15:
                        val = (pc + 12) & MASK32
                    self.mem.write32(a, val)
                offset += 4
                cycles += 1

        if writeback:
            if up:
                self.regs[rn_idx] = (base + count * 4) & MASK32
            else:
                self.regs[rn_idx] = (base - count * 4) & MASK32

        self.cycles += cycles
        return cycles

    def _arm_msr(self, instr):
        spsr = bool(instr & 0x00400000)
        if instr & 0x02000000:
            imm = instr & 0xFF
            rot = ((instr >> 8) & 0xF) * 2
            val = ((imm >> rot) | (imm << (32 - rot))) & MASK32 if rot else imm
        else:
            val = self.regs[instr & 0xF]
        
        mask = 0
        if instr & 0x00080000: mask |= 0xFF000000  # flags
        if instr & 0x00010000: mask |= 0x000000FF  # control

        if spsr:
            mode = self.cpsr & 0x1F
            if mode in self.spsr:
                self.spsr[mode] = (self.spsr[mode] & ~mask) | (val & mask)
        else:
            self.cpsr = (self.cpsr & ~mask) | (val & mask)
        self.cycles += 1
        return 1

    # =========================================================================
    # THUMB INSTRUCTION EXECUTION
    # =========================================================================

    def _step_thumb(self):
        pc = self.regs[15]
        instr = self.mem.read16(pc)
        self.regs[15] = (pc + 2) & MASK32

        # Format 1: Move shifted register
        if (instr & 0xE000) == 0x0000:
            op = (instr >> 11) & 0x3
            if op < 3:
                return self._thumb_shift(instr, pc)
            else:  # Format 2: Add/Sub
                return self._thumb_add_sub(instr, pc)

        # Format 3: Mov/Cmp/Add/Sub immediate
        if (instr & 0xE000) == 0x2000:
            return self._thumb_imm(instr)

        # Format 4: ALU operations
        if (instr & 0xFC00) == 0x4000:
            return self._thumb_alu(instr)

        # Format 5: Hi register / BX
        if (instr & 0xFC00) == 0x4400:
            return self._thumb_hireg(instr, pc)

        # Format 6: PC-relative load
        if (instr & 0xF800) == 0x4800:
            return self._thumb_pc_load(instr, pc)

        # Format 7/8: Load/Store with register offset
        if (instr & 0xF200) == 0x5000:
            return self._thumb_load_store_reg(instr)
        if (instr & 0xF200) == 0x5200:
            return self._thumb_load_store_sign(instr)

        # Format 9: Load/Store with immediate offset
        if (instr & 0xE000) == 0x6000:
            return self._thumb_load_store_imm(instr)

        # Format 10: Load/Store halfword
        if (instr & 0xF000) == 0x8000:
            return self._thumb_load_store_half(instr)

        # Format 11: SP-relative load/store
        if (instr & 0xF000) == 0x9000:
            return self._thumb_sp_load_store(instr)

        # Format 12: Load address (ADD PC/SP)
        if (instr & 0xF000) == 0xA000:
            return self._thumb_load_addr(instr, pc)

        # Format 13: Add offset to SP
        if (instr & 0xFF00) == 0xB000:
            return self._thumb_sp_offset(instr)

        # Format 14: Push/Pop
        if (instr & 0xF600) == 0xB400:
            return self._thumb_push_pop(instr)

        # Format 15: Multiple load/store
        if (instr & 0xF000) == 0xC000:
            return self._thumb_multi(instr)

        # Format 16: Conditional branch
        if (instr & 0xF000) == 0xD000:
            return self._thumb_cond_branch(instr, pc)

        # Format 17: SWI
        if (instr & 0xFF00) == 0xDF00:
            HleBios.handle_swi(self, instr & 0xFF)
            self.cycles += 3
            return 3

        # Format 18: Unconditional branch
        if (instr & 0xF800) == 0xE000:
            offset = instr & 0x7FF
            if offset & 0x400:
                offset |= 0xFFFFF800
                offset -= 0x100000000
            self.regs[15] = (pc + 4 + offset * 2) & MASK32
            self.cycles += 3
            return 3

        # Format 19: Long branch with link (two-instruction)
        if (instr & 0xF800) == 0xF000:
            offset = instr & 0x7FF
            if offset & 0x400:
                offset |= 0xFFFFF800
            self.regs[14] = (pc + 4 + (offset << 12)) & MASK32
            self.cycles += 1
            return 1

        if (instr & 0xF800) == 0xF800:
            offset = instr & 0x7FF
            target = (self.regs[14] + offset * 2) & MASK32
            self.regs[14] = ((pc + 2) | 1) & MASK32
            self.regs[15] = target
            self.cycles += 3
            return 3

        self.cycles += 1
        return 1

    def _thumb_shift(self, instr, pc):
        op = (instr >> 11) & 0x3
        offset = (instr >> 6) & 0x1F
        rs = (instr >> 3) & 0x7
        rd = instr & 0x7
        val = self.regs[rs]
        carry = self.get_flag(FLAG_C)

        if op == 0:  # LSL
            if offset:
                carry = (val >> (32 - offset)) & 1
                val = (val << offset) & MASK32
        elif op == 1:  # LSR
            if offset == 0: offset = 32
            carry = (val >> (offset - 1)) & 1
            val = val >> offset if offset < 32 else 0
        elif op == 2:  # ASR
            if offset == 0: offset = 32
            carry = (val >> (min(offset, 31) - 1)) & 1 if offset else self.get_flag(FLAG_C)
            if val & 0x80000000:
                val = (val >> min(offset, 31)) | (MASK32 << (32 - min(offset, 31)))
                val &= MASK32
            else:
                val = val >> min(offset, 31)

        self.regs[rd] = val & MASK32
        self.set_nz(val & MASK32)
        self.set_flag(FLAG_C, carry)
        self.cycles += 1
        return 1

    def _thumb_add_sub(self, instr, pc):
        op = (instr >> 9) & 0x3
        rs = (instr >> 3) & 0x7
        rd = instr & 0x7
        
        if op & 0x2:  # Immediate
            operand = (instr >> 6) & 0x7
        else:
            operand = self.regs[(instr >> 6) & 0x7]
        
        val = self.regs[rs]
        if op & 1:  # SUB
            result = val - operand
            self._sub_flags(val, operand, result)
        else:  # ADD
            result = val + operand
            self._add_flags(val, operand, result)
        
        self.regs[rd] = result & MASK32
        self.cycles += 1
        return 1

    def _thumb_imm(self, instr):
        op = (instr >> 11) & 0x3
        rd = (instr >> 8) & 0x7
        imm = instr & 0xFF

        if op == 0:  # MOV
            self.regs[rd] = imm
            self.set_nz(imm)
        elif op == 1:  # CMP
            result = self.regs[rd] - imm
            self._sub_flags(self.regs[rd], imm, result)
        elif op == 2:  # ADD
            result = self.regs[rd] + imm
            self._add_flags(self.regs[rd], imm, result)
            self.regs[rd] = result & MASK32
        elif op == 3:  # SUB
            result = self.regs[rd] - imm
            self._sub_flags(self.regs[rd], imm, result)
            self.regs[rd] = result & MASK32

        self.cycles += 1
        return 1

    def _thumb_alu(self, instr):
        op = (instr >> 6) & 0xF
        rs = (instr >> 3) & 0x7
        rd = instr & 0x7
        a = self.regs[rd]
        b = self.regs[rs]
        carry = self.get_flag(FLAG_C)

        if op == 0x0:  # AND
            result = a & b
            self.set_nz(result)
        elif op == 0x1:  # EOR
            result = a ^ b
            self.set_nz(result)
        elif op == 0x2:  # LSL
            shift = b & 0xFF
            if shift:
                if shift < 32:
                    self.set_flag(FLAG_C, (a >> (32 - shift)) & 1)
                    result = (a << shift) & MASK32
                elif shift == 32:
                    self.set_flag(FLAG_C, a & 1)
                    result = 0
                else:
                    self.set_flag(FLAG_C, 0)
                    result = 0
            else:
                result = a
            self.set_nz(result)
        elif op == 0x3:  # LSR
            shift = b & 0xFF
            if shift:
                if shift < 32:
                    self.set_flag(FLAG_C, (a >> (shift - 1)) & 1)
                    result = a >> shift
                elif shift == 32:
                    self.set_flag(FLAG_C, (a >> 31) & 1)
                    result = 0
                else:
                    self.set_flag(FLAG_C, 0)
                    result = 0
            else:
                result = a
            self.set_nz(result)
        elif op == 0x4:  # ASR
            shift = b & 0xFF
            if shift:
                if shift < 32:
                    self.set_flag(FLAG_C, (a >> (shift - 1)) & 1)
                    result = self.s32(a) >> shift
                    result &= MASK32
                else:
                    bit31 = (a >> 31) & 1
                    self.set_flag(FLAG_C, bit31)
                    result = MASK32 if bit31 else 0
            else:
                result = a
            self.set_nz(result)
        elif op == 0x5:  # ADC
            result = a + b + carry
            self._add_flags(a, b + carry, result)
            result &= MASK32
        elif op == 0x6:  # SBC
            result = a - b - (1 - carry)
            self._sub_flags(a, b + (1 - carry), result)
            result &= MASK32
        elif op == 0x7:  # ROR
            shift = b & 0xFF
            if shift:
                shift &= 31
                if shift:
                    result = ((a >> shift) | (a << (32 - shift))) & MASK32
                    self.set_flag(FLAG_C, (result >> 31) & 1)
                else:
                    result = a
                    self.set_flag(FLAG_C, (a >> 31) & 1)
            else:
                result = a
            self.set_nz(result)
        elif op == 0x8:  # TST
            result = a & b
            self.set_nz(result)
            self.regs[rd] = a  # Don't modify
            self.cycles += 1
            return 1
        elif op == 0x9:  # NEG
            result = (0 - b)
            self._sub_flags(0, b, result)
            result &= MASK32
        elif op == 0xA:  # CMP
            result = a - b
            self._sub_flags(a, b, result)
            self.cycles += 1
            return 1
        elif op == 0xB:  # CMN
            result = a + b
            self._add_flags(a, b, result)
            self.cycles += 1
            return 1
        elif op == 0xC:  # ORR
            result = a | b
            self.set_nz(result)
        elif op == 0xD:  # MUL
            result = (a * b) & MASK32
            self.set_nz(result)
        elif op == 0xE:  # BIC
            result = a & ~b
            self.set_nz(result)
        elif op == 0xF:  # MVN
            result = (~b) & MASK32
            self.set_nz(result)
        else:
            result = a

        self.regs[rd] = result & MASK32
        self.cycles += 1
        return 1

    def _thumb_hireg(self, instr, pc):
        op = (instr >> 8) & 0x3
        h1 = (instr >> 7) & 1
        h2 = (instr >> 6) & 1
        rs = ((h2 << 3) | ((instr >> 3) & 0x7))
        rd = ((h1 << 3) | (instr & 0x7))

        val_rs = self.regs[rs]
        if rs == 15:
            val_rs = (pc + 4) & MASK32
        val_rd = self.regs[rd]
        if rd == 15:
            val_rd = (pc + 4) & MASK32

        if op == 0:  # ADD
            self.regs[rd] = (val_rd + val_rs) & MASK32
            if rd == 15:
                self.regs[15] &= ~1
                self.pipeline_valid = False
        elif op == 1:  # CMP
            result = val_rd - val_rs
            self._sub_flags(val_rd, val_rs, result)
        elif op == 2:  # MOV
            self.regs[rd] = val_rs
            if rd == 15:
                self.regs[15] &= ~1
                self.pipeline_valid = False
        elif op == 3:  # BX
            if val_rs & 1:
                self.cpsr |= FLAG_T
                self.regs[15] = val_rs & ~1
            else:
                self.cpsr &= ~FLAG_T
                self.regs[15] = val_rs & ~3
            self.pipeline_valid = False

        self.cycles += 1 if op != 3 else 3
        return 1 if op != 3 else 3

    def _thumb_pc_load(self, instr, pc):
        rd = (instr >> 8) & 0x7
        offset = (instr & 0xFF) * 4
        addr = ((pc + 4) & ~2) + offset
        self.regs[rd] = self.mem.read32(addr)
        self.cycles += 3
        return 3

    def _thumb_load_store_reg(self, instr):
        op = (instr >> 10) & 0x3
        ro = (instr >> 6) & 0x7
        rb = (instr >> 3) & 0x7
        rd = instr & 0x7
        addr = (self.regs[rb] + self.regs[ro]) & MASK32

        if op == 0:  # STR
            self.mem.write32(addr, self.regs[rd])
        elif op == 1:  # STRB
            self.mem.write8(addr, self.regs[rd] & 0xFF)
        elif op == 2:  # LDR
            self.regs[rd] = self.mem.read32(addr)
        elif op == 3:  # LDRB
            self.regs[rd] = self.mem.read8(addr)

        self.cycles += 3
        return 3

    def _thumb_load_store_sign(self, instr):
        op = (instr >> 10) & 0x3
        ro = (instr >> 6) & 0x7
        rb = (instr >> 3) & 0x7
        rd = instr & 0x7
        addr = (self.regs[rb] + self.regs[ro]) & MASK32

        if op == 0:  # STRH
            self.mem.write16(addr, self.regs[rd] & 0xFFFF)
        elif op == 1:  # LDSB
            self.regs[rd] = self.s8(self.mem.read8(addr)) & MASK32
        elif op == 2:  # LDRH
            self.regs[rd] = self.mem.read16(addr)
        elif op == 3:  # LDSH
            self.regs[rd] = self.s16(self.mem.read16(addr)) & MASK32

        self.cycles += 3
        return 3

    def _thumb_load_store_imm(self, instr):
        load = bool(instr & 0x0800)
        byte = bool(instr & 0x1000)
        offset = (instr >> 6) & 0x1F
        rb = (instr >> 3) & 0x7
        rd = instr & 0x7

        if not byte:
            offset *= 4

        addr = (self.regs[rb] + offset) & MASK32

        if load:
            if byte:
                self.regs[rd] = self.mem.read8(addr)
            else:
                self.regs[rd] = self.mem.read32(addr)
        else:
            if byte:
                self.mem.write8(addr, self.regs[rd] & 0xFF)
            else:
                self.mem.write32(addr, self.regs[rd])

        self.cycles += 3
        return 3

    def _thumb_load_store_half(self, instr):
        load = bool(instr & 0x0800)
        offset = ((instr >> 6) & 0x1F) * 2
        rb = (instr >> 3) & 0x7
        rd = instr & 0x7
        addr = (self.regs[rb] + offset) & MASK32

        if load:
            self.regs[rd] = self.mem.read16(addr)
        else:
            self.mem.write16(addr, self.regs[rd] & 0xFFFF)

        self.cycles += 3
        return 3

    def _thumb_sp_load_store(self, instr):
        load = bool(instr & 0x0800)
        rd = (instr >> 8) & 0x7
        offset = (instr & 0xFF) * 4
        addr = (self.regs[13] + offset) & MASK32

        if load:
            self.regs[rd] = self.mem.read32(addr)
        else:
            self.mem.write32(addr, self.regs[rd])

        self.cycles += 3
        return 3

    def _thumb_load_addr(self, instr, pc):
        sp = bool(instr & 0x0800)
        rd = (instr >> 8) & 0x7
        offset = (instr & 0xFF) * 4

        if sp:
            self.regs[rd] = (self.regs[13] + offset) & MASK32
        else:
            self.regs[rd] = (((pc + 4) & ~2) + offset) & MASK32

        self.cycles += 1
        return 1

    def _thumb_sp_offset(self, instr):
        offset = (instr & 0x7F) * 4
        if instr & 0x80:
            self.regs[13] = (self.regs[13] - offset) & MASK32
        else:
            self.regs[13] = (self.regs[13] + offset) & MASK32
        self.cycles += 1
        return 1

    def _thumb_push_pop(self, instr):
        pop = bool(instr & 0x0800)
        pc_lr = bool(instr & 0x0100)
        reg_list = instr & 0xFF
        sp = self.regs[13]

        if pop:
            for i in range(8):
                if reg_list & (1 << i):
                    self.regs[i] = self.mem.read32(sp)
                    sp += 4
            if pc_lr:
                self.regs[15] = self.mem.read32(sp) & ~1
                sp += 4
                self.pipeline_valid = False
            self.regs[13] = sp & MASK32
        else:
            count = bin(reg_list).count('1') + (1 if pc_lr else 0)
            sp -= count * 4
            self.regs[13] = sp & MASK32
            addr = sp
            for i in range(8):
                if reg_list & (1 << i):
                    self.mem.write32(addr, self.regs[i])
                    addr += 4
            if pc_lr:
                self.mem.write32(addr, self.regs[14])

        self.cycles += 3
        return 3

    def _thumb_multi(self, instr):
        load = bool(instr & 0x0800)
        rb = (instr >> 8) & 0x7
        reg_list = instr & 0xFF
        addr = self.regs[rb]

        for i in range(8):
            if reg_list & (1 << i):
                if load:
                    self.regs[i] = self.mem.read32(addr)
                else:
                    self.mem.write32(addr, self.regs[i])
                addr += 4

        self.regs[rb] = addr & MASK32
        self.cycles += 3
        return 3

    def _thumb_cond_branch(self, instr, pc):
        cond = (instr >> 8) & 0xF
        if cond >= 0xE:
            self.cycles += 1
            return 1
        offset = instr & 0xFF
        if offset & 0x80:
            offset |= 0xFFFFFF00
            offset -= 0x100000000
        if self.check_cond(cond):
            self.regs[15] = (pc + 4 + offset * 2) & MASK32
            self.cycles += 3
            return 3
        self.cycles += 1
        return 1


# =============================================================================
# DMA CONTROLLER
# =============================================================================

class DMAController:
    """GBA DMA controller - 4 channels."""

    def __init__(self, mem: MemoryBus):
        self.mem = mem
        self.channels = [DMAChannel(i) for i in range(4)]

    def check_and_run(self, trigger):
        """Check if any DMA channel should trigger and run it."""
        for ch in self.channels:
            if ch.enabled and ch.timing == trigger:
                self._execute(ch)

    def on_io_write(self, offset, val, size):
        """Handle writes to DMA registers."""
        for i, ch in enumerate(self.channels):
            base = REG_DMA0SAD + i * 12
            if offset == base or offset == base + 1:
                # SAD low/high
                if size >= 2:
                    ch.sad = (ch.sad & 0xFFFF0000) | (val & 0xFFFF)
                elif offset == base:
                    ch.sad = (ch.sad & 0xFFFFFF00) | (val & 0xFF)
            elif offset == base + 2 or offset == base + 3:
                if size >= 2:
                    ch.sad = (ch.sad & 0x0000FFFF) | ((val & 0xFFFF) << 16) if offset == base + 2 else ch.sad
            elif offset == base + 4:
                if size >= 4:
                    ch.sad = val & MASK32
            elif offset == base + 4 or offset == base + 5:
                if size >= 2:
                    ch.dad = (ch.dad & 0xFFFF0000) | (val & 0xFFFF)
            elif offset == base + 8:
                if size >= 2:
                    ch.count = val & 0xFFFF
            elif offset == base + 10:
                if size >= 2:
                    ch.control = val & 0xFFFF
                    ch.enabled = bool(val & 0x8000)
                    ch.timing = (val >> 12) & 0x3
                    ch.word_size = 4 if val & 0x0400 else 2
                    ch.dest_ctrl = (val >> 5) & 0x3
                    ch.src_ctrl = (val >> 7) & 0x3
                    ch.irq = bool(val & 0x4000)
                    ch.repeat = bool(val & 0x0200)
                    if ch.enabled and ch.timing == 0:
                        self._execute(ch)

    def _execute(self, ch):
        """Execute a DMA transfer."""
        count = ch.count
        if count == 0:
            count = 0x4000 if ch.index < 3 else 0x10000
        
        src = ch.sad
        dst = ch.dad
        ws = ch.word_size
        
        for _ in range(count):
            if ws == 4:
                self.mem.write32(dst, self.mem.read32(src))
            else:
                self.mem.write16(dst, self.mem.read16(src))
            
            # Source control
            if ch.src_ctrl == 0:
                src += ws
            elif ch.src_ctrl == 1:
                src -= ws
            # 2 = fixed, 3 = prohibited
            
            # Dest control
            if ch.dest_ctrl == 0 or ch.dest_ctrl == 3:
                dst += ws
            elif ch.dest_ctrl == 1:
                dst -= ws
            # 2 = fixed

        ch.sad = src & MASK32
        ch.dad = dst & MASK32 if ch.dest_ctrl != 3 else ch.dad
        
        if not ch.repeat:
            ch.enabled = False


class DMAChannel:
    def __init__(self, index):
        self.index = index
        self.sad = 0
        self.dad = 0
        self.count = 0
        self.control = 0
        self.enabled = False
        self.timing = 0   # 0=immediate, 1=VBlank, 2=HBlank, 3=special
        self.word_size = 2
        self.dest_ctrl = 0
        self.src_ctrl = 0
        self.irq = False
        self.repeat = False


# =============================================================================
# TIMER CONTROLLER
# =============================================================================

class TimerController:
    """GBA timer unit - 4 timers."""

    PRESCALER = [1, 64, 256, 1024]

    def __init__(self, mem: MemoryBus):
        self.mem = mem
        self.timers = [TimerState() for _ in range(4)]
        self.pending_irq = 0

    def tick(self, cycles):
        """Advance timers by the given number of CPU cycles."""
        for i, t in enumerate(self.timers):
            if not t.enabled:
                continue
            if t.cascade and i > 0:
                continue  # Cascade timers are clocked by overflow of previous

            t.sub_count += cycles
            prescale = self.PRESCALER[t.prescaler]
            
            while t.sub_count >= prescale:
                t.sub_count -= prescale
                t.counter += 1
                if t.counter > 0xFFFF:
                    t.counter = t.reload
                    if t.irq:
                        self.pending_irq |= (IRQ_TIMER0 << i)
                    # Cascade: clock next timer
                    if i < 3 and self.timers[i + 1].enabled and self.timers[i + 1].cascade:
                        self.timers[i + 1].counter += 1
                        if self.timers[i + 1].counter > 0xFFFF:
                            self.timers[i + 1].counter = self.timers[i + 1].reload
                            if self.timers[i + 1].irq:
                                self.pending_irq |= (IRQ_TIMER0 << (i + 1))

    def on_io_write(self, offset, val, size):
        for i in range(4):
            cnt_l = REG_TM0CNT_L + i * 4
            cnt_h = REG_TM0CNT_H + i * 4
            if offset == cnt_l and size >= 2:
                self.timers[i].reload = val & 0xFFFF
            elif offset == cnt_h and size >= 2:
                old_en = self.timers[i].enabled
                self.timers[i].prescaler = val & 0x3
                self.timers[i].cascade = bool(val & 0x4)
                self.timers[i].irq = bool(val & 0x40)
                self.timers[i].enabled = bool(val & 0x80)
                if not old_en and self.timers[i].enabled:
                    self.timers[i].counter = self.timers[i].reload
                    self.timers[i].sub_count = 0


class TimerState:
    def __init__(self):
        self.counter = 0
        self.reload = 0
        self.prescaler = 0
        self.cascade = False
        self.irq = False
        self.enabled = False
        self.sub_count = 0


# =============================================================================
# PPU (LCD Controller)
# =============================================================================

class PPU:
    """GBA PPU - renders 240x160 @ 60Hz."""

    def __init__(self, mem: MemoryBus):
        self.mem = mem
        self.scanline = 0
        self.dot = 0
        self.framebuffer = bytearray(SCREEN_W * SCREEN_H * 3)  # RGB888
        self.frame_ready = False
        self.pending_irq = 0

    def rgb555_to_rgb888(self, color):
        r = (color & 0x1F) << 3
        g = ((color >> 5) & 0x1F) << 3
        b = ((color >> 10) & 0x1F) << 3
        return r, g, b

    def step(self, cycles):
        """Advance PPU by given CPU cycles."""
        self.dot += cycles
        
        while self.dot >= 1232:
            self.dot -= 1232
            self._end_scanline()

    def _end_scanline(self):
        vcount = self.scanline
        
        if vcount < 160:
            self._render_scanline(vcount)

        self.scanline += 1
        
        if self.scanline == 160:
            # VBlank start
            dispstat = self.mem.read_io16(REG_DISPSTAT)
            dispstat |= 0x0001  # VBlank flag
            self.mem._write_io16(REG_DISPSTAT, dispstat)
            if dispstat & 0x0008:  # VBlank IRQ enable
                self.pending_irq |= IRQ_VBLANK
            self.frame_ready = True

        if self.scanline >= 228:
            self.scanline = 0
            dispstat = self.mem.read_io16(REG_DISPSTAT)
            dispstat &= ~0x0001
            self.mem._write_io16(REG_DISPSTAT, dispstat)

        # Update VCOUNT
        self.mem._write_io16(REG_VCOUNT, self.scanline)
        
        # VCount match
        dispstat = self.mem.read_io16(REG_DISPSTAT)
        lyc = (dispstat >> 8) & 0xFF
        if self.scanline == lyc:
            dispstat |= 0x0004
            if dispstat & 0x0020:
                self.pending_irq |= IRQ_VCOUNT
        else:
            dispstat &= ~0x0004
        self.mem._write_io16(REG_DISPSTAT, dispstat)

    def _render_scanline(self, y):
        dispcnt = self.mem.read_io16(REG_DISPCNT)
        mode = dispcnt & 0x7
        
        if mode == 0:
            self._render_mode0(y, dispcnt)
        elif mode == 1:
            self._render_mode1(y, dispcnt)
        elif mode == 2:
            self._render_mode2(y, dispcnt)
        elif mode == 3:
            self._render_mode3(y)
        elif mode == 4:
            self._render_mode4(y, dispcnt)
        elif mode == 5:
            self._render_mode5(y, dispcnt)

        # Render sprites on top if enabled
        if dispcnt & 0x1000:
            self._render_sprites(y)

    def _render_mode3(self, y):
        """Mode 3: 240x160 16-bit bitmap."""
        vram = self.mem.vram
        fb = self.framebuffer
        base = y * 480  # 240 * 2
        fb_off = y * SCREEN_W * 3
        for x in range(SCREEN_W):
            off = base + x * 2
            color = vram[off] | (vram[off + 1] << 8)
            r, g, b = self.rgb555_to_rgb888(color)
            fb[fb_off] = r
            fb[fb_off + 1] = g
            fb[fb_off + 2] = b
            fb_off += 3

    def _render_mode4(self, y, dispcnt):
        """Mode 4: 240x160 8-bit palettized bitmap (double buffered)."""
        vram = self.mem.vram
        pal = self.mem.palette
        fb = self.framebuffer
        frame = 0xA000 if (dispcnt & 0x0010) else 0
        base = frame + y * 240
        fb_off = y * SCREEN_W * 3
        for x in range(SCREEN_W):
            idx = vram[base + x]
            color = pal[idx * 2] | (pal[idx * 2 + 1] << 8)
            r, g, b = self.rgb555_to_rgb888(color)
            fb[fb_off] = r
            fb[fb_off + 1] = g
            fb[fb_off + 2] = b
            fb_off += 3

    def _render_mode5(self, y, dispcnt):
        """Mode 5: 160x128 16-bit bitmap (double buffered)."""
        if y >= 128:
            fb_off = y * SCREEN_W * 3
            for x in range(SCREEN_W):
                self.framebuffer[fb_off:fb_off+3] = b'\x00\x00\x00'
                fb_off += 3
            return
        vram = self.mem.vram
        fb = self.framebuffer
        frame = 0xA000 if (dispcnt & 0x0010) else 0
        base = frame + y * 320  # 160 * 2
        fb_off = y * SCREEN_W * 3
        for x in range(160):
            off = base + x * 2
            color = vram[off] | (vram[off + 1] << 8)
            r, g, b = self.rgb555_to_rgb888(color)
            fb[fb_off] = r
            fb[fb_off + 1] = g
            fb[fb_off + 2] = b
            fb_off += 3
        for x in range(160, SCREEN_W):
            fb[fb_off:fb_off+3] = b'\x00\x00\x00'
            fb_off += 3

    def _render_mode0(self, y, dispcnt):
        """Mode 0: 4 regular tile backgrounds."""
        fb = self.framebuffer
        fb_off = y * SCREEN_W * 3
        
        # Clear scanline with backdrop color
        backdrop = self.mem.palette[0] | (self.mem.palette[1] << 8)
        r, g, b = self.rgb555_to_rgb888(backdrop)
        for x in range(SCREEN_W):
            fb[fb_off + x*3] = r
            fb[fb_off + x*3 + 1] = g
            fb[fb_off + x*3 + 2] = b

        # Render enabled backgrounds (BG0-BG3) back to front by priority
        bgs = []
        for bg in range(4):
            if dispcnt & (0x0100 << bg):
                bgcnt = self.mem.read_io16(REG_BG0CNT + bg * 2)
                pri = bgcnt & 0x3
                bgs.append((pri, bg, bgcnt))
        bgs.sort(key=lambda x: (-x[0], -x[1]))  # Lower priority number = higher priority, render last

        for pri, bg, bgcnt in bgs:
            self._render_text_bg(y, bg, bgcnt, fb, fb_off)

    def _render_text_bg(self, y, bg_num, bgcnt, fb, fb_off):
        """Render a text-mode background scanline."""
        vram = self.mem.vram
        pal = self.mem.palette
        
        char_base = ((bgcnt >> 2) & 0x3) * 0x4000
        screen_base = ((bgcnt >> 8) & 0x1F) * 0x800
        color_mode = bool(bgcnt & 0x0080)  # 0=4bpp, 1=8bpp
        size = (bgcnt >> 14) & 0x3
        
        # BG size in tiles
        sizes_w = [32, 64, 32, 64]
        sizes_h = [32, 32, 64, 64]
        map_w = sizes_w[size]
        map_h = sizes_h[size]
        
        hofs = self.mem.read_io16(REG_BG0HOFS + bg_num * 4) & 0x1FF
        vofs = self.mem.read_io16(REG_BG0VOFS + bg_num * 4) & 0x1FF

        py = (y + vofs) % (map_h * 8)
        tile_y = py // 8
        fine_y = py % 8

        for x in range(SCREEN_W):
            px = (x + hofs) % (map_w * 8)
            tile_x = px // 8
            fine_x = px % 8

            # Determine which screen block
            screen_block = 0
            tx = tile_x
            ty = tile_y
            if map_w == 64 and tile_x >= 32:
                screen_block += 1
                tx -= 32
            if map_h == 64 and tile_y >= 32:
                screen_block += 2
                ty -= 32

            map_addr = screen_base + screen_block * 0x800 + (ty * 32 + tx) * 2
            tile_entry = vram[map_addr] | (vram[map_addr + 1] << 8)
            
            tile_num = tile_entry & 0x3FF
            h_flip = bool(tile_entry & 0x0400)
            v_flip = bool(tile_entry & 0x0800)
            pal_bank = (tile_entry >> 12) & 0xF

            fy = (7 - fine_y) if v_flip else fine_y
            fx = (7 - fine_x) if h_flip else fine_x

            if color_mode:  # 8bpp
                pixel_addr = char_base + tile_num * 64 + fy * 8 + fx
                if pixel_addr < VRAM_SIZE:
                    idx = vram[pixel_addr]
                    if idx == 0:
                        continue
                    color = pal[idx * 2] | (pal[idx * 2 + 1] << 8)
                else:
                    continue
            else:  # 4bpp
                pixel_addr = char_base + tile_num * 32 + fy * 4 + fx // 2
                if pixel_addr < VRAM_SIZE:
                    byte = vram[pixel_addr]
                    idx = (byte >> 4) if (fx & 1) else (byte & 0xF)
                    if idx == 0:
                        continue
                    pal_idx = pal_bank * 16 + idx
                    color = pal[pal_idx * 2] | (pal[pal_idx * 2 + 1] << 8)
                else:
                    continue

            r, g, b = self.rgb555_to_rgb888(color)
            off = fb_off + x * 3
            fb[off] = r
            fb[off + 1] = g
            fb[off + 2] = b

    def _render_mode1(self, y, dispcnt):
        """Mode 1: BG0,BG1 text, BG2 affine."""
        fb = self.framebuffer
        fb_off = y * SCREEN_W * 3
        backdrop = self.mem.palette[0] | (self.mem.palette[1] << 8)
        r, g, b = self.rgb555_to_rgb888(backdrop)
        for x in range(SCREEN_W):
            fb[fb_off + x*3] = r
            fb[fb_off + x*3 + 1] = g
            fb[fb_off + x*3 + 2] = b

        bgs = []
        for bg in [0, 1]:
            if dispcnt & (0x0100 << bg):
                bgcnt = self.mem.read_io16(REG_BG0CNT + bg * 2)
                pri = bgcnt & 0x3
                bgs.append((pri, bg, bgcnt, False))
        if dispcnt & 0x0400:  # BG2
            bgcnt = self.mem.read_io16(REG_BG2CNT)
            pri = bgcnt & 0x3
            bgs.append((pri, 2, bgcnt, True))
        bgs.sort(key=lambda x: (-x[0], -x[1]))

        for pri, bg, bgcnt, affine in bgs:
            if affine:
                self._render_affine_bg(y, bg, bgcnt, fb, fb_off)
            else:
                self._render_text_bg(y, bg, bgcnt, fb, fb_off)

    def _render_mode2(self, y, dispcnt):
        """Mode 2: BG2,BG3 affine."""
        fb = self.framebuffer
        fb_off = y * SCREEN_W * 3
        backdrop = self.mem.palette[0] | (self.mem.palette[1] << 8)
        r, g, b = self.rgb555_to_rgb888(backdrop)
        for x in range(SCREEN_W):
            fb[fb_off + x*3] = r
            fb[fb_off + x*3 + 1] = g
            fb[fb_off + x*3 + 2] = b

        bgs = []
        for bg in [2, 3]:
            if dispcnt & (0x0100 << bg):
                bgcnt = self.mem.read_io16(REG_BG0CNT + bg * 2)
                pri = bgcnt & 0x3
                bgs.append((pri, bg, bgcnt))
        bgs.sort(key=lambda x: (-x[0], -x[1]))
        for pri, bg, bgcnt in bgs:
            self._render_affine_bg(y, bg, bgcnt, fb, fb_off)

    def _render_affine_bg(self, y, bg_num, bgcnt, fb, fb_off):
        """Render an affine (rotation/scaling) background."""
        vram = self.mem.vram
        pal = self.mem.palette
        
        char_base = ((bgcnt >> 2) & 0x3) * 0x4000
        screen_base = ((bgcnt >> 8) & 0x1F) * 0x800
        wrap = bool(bgcnt & 0x2000)
        size_bits = (bgcnt >> 14) & 0x3
        sizes = [16, 32, 64, 128]
        map_size = sizes[size_bits]
        
        if bg_num == 2:
            pa = ARM7TDMI.s16(self.mem.read_io16(REG_BG2PA))
            pb = ARM7TDMI.s16(self.mem.read_io16(REG_BG2PB))
            pc = ARM7TDMI.s16(self.mem.read_io16(REG_BG2PC))
            pd = ARM7TDMI.s16(self.mem.read_io16(REG_BG2PD))
            ref_x = self.mem.read32(IO_START + REG_BG2X)
            ref_y = self.mem.read32(IO_START + REG_BG2Y)
        else:
            pa = ARM7TDMI.s16(self.mem.read_io16(REG_BG3PA))
            pb = ARM7TDMI.s16(self.mem.read_io16(REG_BG3PB))
            pc = ARM7TDMI.s16(self.mem.read_io16(REG_BG3PC))
            pd = ARM7TDMI.s16(self.mem.read_io16(REG_BG3PD))
            ref_x = self.mem.read32(IO_START + REG_BG3X)
            ref_y = self.mem.read32(IO_START + REG_BG3Y)

        # Sign extend 28-bit fixed point
        if ref_x & 0x08000000: ref_x |= 0xF0000000; ref_x -= 0x100000000
        if ref_y & 0x08000000: ref_y |= 0xF0000000; ref_y -= 0x100000000

        cx = ref_x + pb * y
        cy = ref_y + pd * y
        
        pixel_size = map_size * 8

        for x in range(SCREEN_W):
            tx = (cx + pa * x) >> 8
            ty = (cy + pc * x) >> 8

            if wrap:
                tx %= pixel_size
                ty %= pixel_size
            elif tx < 0 or tx >= pixel_size or ty < 0 or ty >= pixel_size:
                continue

            tile_x = tx // 8
            tile_y = ty // 8
            fine_x = tx % 8
            fine_y = ty % 8

            map_addr = screen_base + tile_y * map_size + tile_x
            if map_addr < VRAM_SIZE:
                tile_num = vram[map_addr]
            else:
                continue

            pixel_addr = char_base + tile_num * 64 + fine_y * 8 + fine_x
            if pixel_addr < VRAM_SIZE:
                idx = vram[pixel_addr]
                if idx == 0:
                    continue
                color = pal[idx * 2] | (pal[idx * 2 + 1] << 8)
                r, g, b = self.rgb555_to_rgb888(color)
                off = fb_off + x * 3
                fb[off] = r
                fb[off + 1] = g
                fb[off + 2] = b

    def _render_sprites(self, y):
        """Render OBJ (sprite) layer for scanline y."""
        oam = self.mem.oam
        vram = self.mem.vram
        pal = self.mem.palette
        fb = self.framebuffer
        fb_off = y * SCREEN_W * 3
        dispcnt = self.mem.read_io16(REG_DISPCNT)
        obj_mapping = bool(dispcnt & 0x0040)  # 1D mapping

        for i in range(127, -1, -1):  # Lower OAM index = higher priority
            base = i * 8
            attr0 = oam[base] | (oam[base + 1] << 8)
            attr1 = oam[base + 2] | (oam[base + 3] << 8)
            attr2 = oam[base + 4] | (oam[base + 5] << 8)

            # Check if sprite is disabled
            rot_scale = bool(attr0 & 0x0100)
            double_size = bool(attr0 & 0x0200)
            if not rot_scale and double_size:
                continue  # Hidden

            obj_y = attr0 & 0xFF
            shape = (attr0 >> 14) & 0x3
            color_mode = bool(attr0 & 0x2000)  # 0=4bpp, 1=8bpp
            obj_size = (attr1 >> 14) & 0x3

            # Sprite dimensions lookup
            size_table = [
                [(8,8),(16,16),(32,32),(64,64)],    # Square
                [(16,8),(32,8),(32,16),(64,32)],     # Horizontal
                [(8,16),(8,32),(16,32),(32,64)],     # Vertical
                [(8,8),(8,8),(8,8),(8,8)],           # Prohibited
            ]
            w, h = size_table[shape][obj_size]

            # Check Y range
            if obj_y > 160:
                obj_y -= 256
            if y < obj_y or y >= obj_y + h:
                continue

            obj_x = attr1 & 0x1FF
            if obj_x >= 240:
                obj_x -= 512
            h_flip = bool(attr1 & 0x1000) and not rot_scale
            v_flip = bool(attr1 & 0x2000) and not rot_scale
            tile_num = attr2 & 0x3FF
            pal_bank = (attr2 >> 12) & 0xF
            # priority = (attr2 >> 10) & 0x3  # For proper priority sorting

            sprite_y = y - obj_y
            if v_flip:
                sprite_y = h - 1 - sprite_y

            tile_row = sprite_y // 8
            fine_y = sprite_y % 8

            for sx in range(w):
                screen_x = obj_x + sx
                if screen_x < 0 or screen_x >= SCREEN_W:
                    continue

                sprite_x = (w - 1 - sx) if h_flip else sx
                tile_col = sprite_x // 8
                fine_x = sprite_x % 8

                if obj_mapping:  # 1D
                    if color_mode:
                        t = tile_num + tile_row * (w // 8) * 2 + tile_col * 2
                    else:
                        t = tile_num + tile_row * (w // 8) + tile_col
                else:  # 2D
                    if color_mode:
                        t = tile_num + tile_row * 32 + tile_col * 2
                    else:
                        t = tile_num + tile_row * 32 + tile_col

                obj_base = 0x10000  # OBJ tiles start at 0x06010000
                if color_mode:  # 8bpp
                    pixel_addr = obj_base + t * 32 + fine_y * 8 + fine_x
                    if pixel_addr < VRAM_SIZE:
                        idx = vram[pixel_addr]
                        if idx == 0:
                            continue
                        # OBJ palette is at 0x05000200
                        pal_off = 0x200 + idx * 2
                        color = pal[pal_off] | (pal[pal_off + 1] << 8)
                    else:
                        continue
                else:  # 4bpp
                    pixel_addr = obj_base + t * 32 + fine_y * 4 + fine_x // 2
                    if pixel_addr < VRAM_SIZE:
                        byte = vram[pixel_addr]
                        idx = (byte >> 4) if (fine_x & 1) else (byte & 0xF)
                        if idx == 0:
                            continue
                        pal_off = 0x200 + (pal_bank * 16 + idx) * 2
                        color = pal[pal_off] | (pal[pal_off + 1] << 8)
                    else:
                        continue

                r, g, b = self.rgb555_to_rgb888(color)
                off = fb_off + screen_x * 3
                fb[off] = r
                fb[off + 1] = g
                fb[off + 2] = b


# =============================================================================
# GBA SYSTEM
# =============================================================================

class GBASystem:
    """Top-level GBA system tying all components together."""

    def __init__(self):
        self.mem = MemoryBus()
        self.cpu = ARM7TDMI(self.mem)
        self.ppu = PPU(self.mem)
        self.dma = DMAController(self.mem)
        self.timers = TimerController(self.mem)
        self.keystate = 0x03FF  # All keys released
        
        self.is_loaded = False
        self.is_running = False
        self.frame_count = 0
        
        # Wire IO write hook
        self.mem.io_write_hook = self._io_write_hook

    def _io_write_hook(self, offset, val, size):
        """Handle side effects of IO writes."""
        # DMA
        if 0xB0 <= offset <= 0xDF:
            self.dma.on_io_write(offset, val, size)
        # Timers
        if 0x100 <= offset <= 0x10F:
            self.timers.on_io_write(offset, val, size)
        # HALTCNT
        if offset == REG_HALTCNT:
            self.cpu.halted = True

    def load_rom(self, filepath: str) -> bool:
        try:
            with open(filepath, 'rb') as f:
                data = f.read()
            if len(data) < 192:  # Minimum GBA ROM header
                return False
            self.mem.load_rom(data)
            self.cpu = ARM7TDMI(self.mem)
            self.ppu = PPU(self.mem)
            self.mem.io_write_hook = self._io_write_hook
            self.is_loaded = True
            self.is_running = False
            self.frame_count = 0
            
            # Set initial DISPCNT (some ROMs expect this)
            # Default mode 0
            self.mem._write_io16(REG_KEYINPUT, 0x03FF)
            return True
        except Exception as e:
            print(f"ROM load error: {e}")
            return False

    def set_key(self, key_bit, pressed):
        if pressed:
            self.keystate &= ~key_bit
        else:
            self.keystate |= key_bit
        self.mem._write_io16(REG_KEYINPUT, self.keystate)

    def run_frame(self):
        """Run one full frame (280896 cycles)."""
        if not self.is_loaded or not self.is_running:
            return
        
        cpu = self.cpu
        ppu = self.ppu
        timers = self.timers
        target = cpu.total_cycles + CYCLES_PER_FRAME

        while cpu.total_cycles < target:
            # Check IRQs
            if not cpu.halted:
                cycles = cpu.step()
            else:
                cycles = 1
                cpu.cycles += 1
                # Check if we should wake from halt
                ie = self.mem.read_io16(REG_IE)
                iff = self.mem.read_io16(REG_IF)
                if ie & iff:
                    cpu.halted = False
                    cpu.waiting_vblank = False

            cpu.total_cycles += cycles
            
            # Tick PPU
            ppu.step(cycles)
            
            # Tick timers
            timers.tick(cycles)
            
            # Process pending IRQs
            irq = ppu.pending_irq | timers.pending_irq
            if irq:
                ppu.pending_irq = 0
                timers.pending_irq = 0
                current_if = self.mem.read_io16(REG_IF)
                self.mem._write_io16(REG_IF, current_if | irq)
                
                ime = self.mem.read_io16(REG_IME)
                ie = self.mem.read_io16(REG_IE)
                if ime and (ie & irq):
                    if cpu.waiting_vblank and (irq & IRQ_VBLANK):
                        cpu.halted = False
                        cpu.waiting_vblank = False
                    if not (cpu.cpsr & FLAG_I):
                        cpu.fire_irq()

            # DMA VBlank
            if ppu.frame_ready:
                self.dma.check_and_run(1)  # VBlank DMA

        self.frame_count += 1


# =============================================================================
# GUI
# =============================================================================

class GBAEmulatorGUI(tk.Tk):
    """AC Holdings GBA Emulator - Tkinter Frontend."""

    KEY_MAP = {
        'z': KEY_A, 'x': KEY_B,
        'Return': KEY_START, 'BackSpace': KEY_SELECT,
        'Up': KEY_UP, 'Down': KEY_DOWN,
        'Left': KEY_LEFT, 'Right': KEY_RIGHT,
        'a': KEY_L, 's': KEY_R,
    }

    def __init__(self):
        super().__init__()
        self.title("AC Holdings GBA EMULATOR v1.0")
        self.configure(bg="#1a1a2e")
        self.resizable(True, True)

        self.gba = GBASystem()
        self.fps = 0.0
        self.last_time = time.time()
        self.frame_times = []
        self.emu_thread = None
        self.running_lock = threading.Lock()

        self._build_menu()
        self._build_screen()
        self._build_status_bar()
        self._bind_keys()
        
        # Create blank image
        self.img = Image.new('RGB', (SCREEN_W, SCREEN_H), (0, 0, 0))
        self.tk_img = ImageTk.PhotoImage(self.img)
        self.canvas.create_image(0, 0, anchor=tk.NW, image=self.tk_img, tags="screen")

        self._update_loop()

    def _build_menu(self):
        menubar = tk.Menu(self)
        
        file_menu = tk.Menu(menubar, tearoff=0)
        file_menu.add_command(label="Load ROM...", command=self._load_rom, accelerator="Ctrl+O")
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.quit)
        menubar.add_cascade(label="File", menu=file_menu)

        emu_menu = tk.Menu(menubar, tearoff=0)
        emu_menu.add_command(label="Play / Pause", command=self._toggle_play, accelerator="Space")
        emu_menu.add_command(label="Reset", command=self._reset)
        menubar.add_cascade(label="Emulation", menu=emu_menu)

        scale_menu = tk.Menu(menubar, tearoff=0)
        for s in [1, 2, 3, 4]:
            scale_menu.add_command(label=f"{s}x", command=lambda s=s: self._set_scale(s))
        menubar.add_cascade(label="Video", menu=scale_menu)

        help_menu = tk.Menu(menubar, tearoff=0)
        help_menu.add_command(label="Controls", command=self._show_controls)
        help_menu.add_command(label="About", command=self._show_about)
        menubar.add_cascade(label="Help", menu=help_menu)

        self.config(menu=menubar)
        self.bind_all("<Control-o>", lambda e: self._load_rom())
        self.bind_all("<space>", lambda e: self._toggle_play())

    def _build_screen(self):
        self.screen_frame = tk.Frame(self, bg="#0f0f23", bd=2, relief=tk.SUNKEN)
        self.screen_frame.pack(expand=True, fill=tk.BOTH, padx=8, pady=8)
        
        self.canvas = tk.Canvas(
            self.screen_frame,
            width=SCREEN_W * SCALE,
            height=SCREEN_H * SCALE,
            bg="black",
            highlightthickness=0,
        )
        self.canvas.pack(expand=True)

        self.info_text = self.canvas.create_text(
            SCREEN_W * SCALE // 2, SCREEN_H * SCALE // 2,
            text="AC HOLDINGS GBA EMULATOR v1.0\n\nFile → Load ROM to begin",
            fill="#00ff88", font=("Courier", 14, "bold"), justify=tk.CENTER
        )

    def _build_status_bar(self):
        sf = tk.Frame(self, bg="#16213e")
        sf.pack(side=tk.BOTTOM, fill=tk.X)
        
        self.status_left = tk.Label(sf, text="Status: Idle", bg="#16213e", fg="#00ff88",
                                     font=("Courier", 10), anchor="w")
        self.status_left.pack(side=tk.LEFT, padx=8, pady=3)
        
        self.status_right = tk.Label(sf, text="FPS: 0.00 | No ROM", bg="#16213e", fg="#00ff88",
                                      font=("Courier", 10), anchor="e")
        self.status_right.pack(side=tk.RIGHT, padx=8, pady=3)

    def _bind_keys(self):
        self.bind("<KeyPress>", self._key_down)
        self.bind("<KeyRelease>", self._key_up)
        self.focus_set()

    def _key_down(self, event):
        key = event.keysym
        if key in self.KEY_MAP:
            self.gba.set_key(self.KEY_MAP[key], True)

    def _key_up(self, event):
        key = event.keysym
        if key in self.KEY_MAP:
            self.gba.set_key(self.KEY_MAP[key], False)

    def _load_rom(self):
        filepath = filedialog.askopenfilename(
            title="Select GBA ROM",
            filetypes=[("GBA ROMs", "*.gba"), ("All Files", "*.*")]
        )
        if filepath:
            if self.gba.load_rom(filepath):
                name = os.path.basename(filepath)
                # Read game title from ROM header
                title = self.gba.mem.rom[0xA0:0xAC].decode('ascii', errors='replace').strip('\x00')
                self.title(f"AC Holdings GBA EMU - {title or name}")
                self.canvas.itemconfig(self.info_text, text=f"ROM: {title or name}\n\nPress Space to Play")
                self.status_left.config(text="Status: Loaded")
                self.status_right.config(text=f"ROM: {name}")
            else:
                messagebox.showerror("Error", "Failed to load ROM file.")

    def _toggle_play(self):
        if not self.gba.is_loaded:
            return
        self.gba.is_running = not self.gba.is_running
        if self.gba.is_running:
            self.status_left.config(text="Status: Running")
            self.canvas.itemconfig(self.info_text, text="")
            self.last_time = time.time()
            self.frame_times.clear()
        else:
            self.status_left.config(text="Status: Paused")

    def _reset(self):
        if self.gba.is_loaded:
            rom_data = bytes(self.gba.mem.rom)
            self.gba = GBASystem()
            self.gba.mem.load_rom(rom_data)
            self.gba.is_loaded = True
            self.gba.is_running = False
            self.gba.cpu.regs[15] = 0x08000000
            self.gba.cpu.regs[13] = 0x03007F00
            self.gba.mem._write_io16(REG_KEYINPUT, 0x03FF)
            self.gba.mem.io_write_hook = self.gba._io_write_hook
            self.status_left.config(text="Status: Reset")
            self.canvas.itemconfig(self.info_text, text="RESET\nPress Space")

    def _set_scale(self, s):
        global SCALE
        SCALE = s
        self.canvas.config(width=SCREEN_W * SCALE, height=SCREEN_H * SCALE)

    def _show_controls(self):
        messagebox.showinfo("Controls",
            "D-Pad: Arrow Keys\n"
            "A: Z\nB: X\n"
            "L: A\nR: S\n"
            "Start: Enter\nSelect: Backspace\n\n"
            "Space: Play/Pause\nCtrl+O: Load ROM")

    def _show_about(self):
        messagebox.showinfo("About",
            "AC Holdings GBA Emulator v1.0\n"
            "(C) A.C Holdings / Team Flames 1999-2026\n\n"
            "ARM7TDMI CPU Core\n"
            "PPU: Modes 0-5, Sprites, Affine\n"
            "HLE BIOS, DMA, Timers\n\n"
            "Built with Python + Tkinter + Pillow")

    def _update_loop(self):
        """Main update loop - runs emulation and updates display."""
        if self.gba.is_running:
            t0 = time.time()
            
            # Run one frame
            self.gba.run_frame()
            
            # Update display if frame is ready
            if self.gba.ppu.frame_ready:
                self.gba.ppu.frame_ready = False
                self._draw_frame()
            
            # FPS tracking
            t1 = time.time()
            self.frame_times.append(t1 - t0)
            if len(self.frame_times) > 30:
                self.frame_times.pop(0)
            if self.frame_times:
                avg = sum(self.frame_times) / len(self.frame_times)
                self.fps = 1.0 / avg if avg > 0 else 0
            
            # Update status
            if self.gba.frame_count % 15 == 0:
                mode = self.gba.mem.read_io16(REG_DISPCNT) & 7
                pc = self.gba.cpu.regs[15]
                thumb = "T" if self.gba.cpu.in_thumb() else "A"
                self.status_right.config(
                    text=f"FPS: {self.fps:.1f} | Mode {mode} | PC: 0x{pc:08X} [{thumb}]"
                )

            # Target ~60fps, subtract execution time
            elapsed = (time.time() - t0) * 1000
            delay = max(1, int(16.67 - elapsed))
        else:
            delay = 33  # ~30fps idle polling

        self.after(delay, self._update_loop)

    def _draw_frame(self):
        """Convert framebuffer to Tk image and display."""
        self.img = Image.frombytes('RGB', (SCREEN_W, SCREEN_H), bytes(self.gba.ppu.framebuffer))
        if SCALE != 1:
            self.img = self.img.resize((SCREEN_W * SCALE, SCREEN_H * SCALE), Image.NEAREST)
        self.tk_img = ImageTk.PhotoImage(self.img)
        self.canvas.delete("screen")
        self.canvas.create_image(0, 0, anchor=tk.NW, image=self.tk_img, tags="screen")


# =============================================================================
# ENTRY POINT
# =============================================================================

if __name__ == "__main__":
    print("=" * 50)
    print(" AC Holdings GBA Emulator v1.0")
    print(" (C) A.C Holdings / Team Flames 1999-2026")
    print(" ARM7TDMI | PPU Modes 0-5 | HLE BIOS")
    print("=" * 50)
    app = GBAEmulatorGUI()
    app.mainloop()
