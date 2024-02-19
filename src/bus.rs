#![allow(unused)]

use crate::{
    cpu::CPU,
    ppu::PPU,
    cartridge::Cartridge,
    memory::Memory,
};

struct ClockCounter {
    value: u32,
}

impl ClockCounter {

    pub fn new() -> ClockCounter {
        ClockCounter {
            value: 0,
        }
    }

    pub fn increment(&mut self) {
        self.value += 1;
    }

    pub fn decrement(&mut self) {
        self.value -= 1;
    }

}

pub struct Bus {
    cpu_ram: Memory,
    system_clock_counter: ClockCounter,
}

impl Bus {

    pub fn new() -> Bus {
        Bus {
           cpu_ram: Memory::new(),
           system_clock_counter: ClockCounter::new(),
        }
    }

    pub fn cpu_write(&mut self, addr: u16, data: u8) {
        if (addr <= 0x1FFF) {
            // System RAM Address Range. The range covers 8KB, though only 2KB
            // is available. The 2KB is mirrored through this address range.
            // Using bitwise AND to mask the bottom 11 bits is the same as
            // addr % 2048.
            self.cpu_ram.write(addr, data);
        } else if (addr >= 0x2000 && addr <= 0x3FFF) {
            // For future implementation.
        }
    }

    pub fn cpu_read(&self, addr: u16) -> u8 {
        self.cpu_ram.read(addr)
    }
}
