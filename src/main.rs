#![allow(unused)]

use std::collections::HashMap;

use nes_emu::{cpu::{Flags, Registers, CPU}, *};

fn main() {
    let mut bus = bus::Bus::new();
    let mut cpu = CPU::new(&mut bus);
    cpu.bus.cpu_write(0x00A3, 10);

    let data: u8 = cpu.bus.cpu_read(0x00A3);
    println!(" READ {}: {}", 0x00A3 & 0x07FF, data);

    cpu.reg.pc = 0x0100;

    let pc = cpu.reg.pc;

    println!("pc: {:#06x}", pc);
    println!("({:#06x} >> {}) & 0x00FF: {:#04x}", pc, 8, ((pc >> 8) & 0x00FF) as u8);
    println!("{:#06x} & 0x00FF: {:#04x}", pc, (pc & 0x00FF) as u8);
}
