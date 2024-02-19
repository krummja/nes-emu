#![allow(unused, arithmetic_overflow, overflowing_literals)]
/// Emulation of the 6502 Microprocessor used in the
/// Nintendo Entertainment System

use bitflags;
use impl_ops::{self, impl_op};
use std::collections::HashMap;
use std::ops::{Add, Sub, BitOr};
use crate::bus::Bus;


#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Flags(u8);

bitflags::bitflags! {
    impl Flags: u8 {
        const C = (1 << 0);
        const Z = (1 << 1);
        const I = (1 << 2);
        const D = (1 << 3);
        const B = (1 << 4);
        const U = (1 << 5);
        const V = (1 << 6);
        const N = (1 << 7);
    }
}

#[derive(Copy, Clone)]
pub struct Instruction<'a> {
    pub n: &'a str,
    pub o: fn(&mut CPU<'a>) -> u8,
    pub m: fn(&mut CPU<'a>) -> u8,
    pub c: u8,
}

pub struct Registers {
    pub accum: u8,
    pub x: u8,
    pub y: u8,
    pub stkp: u8,
    pub pc: u16,
    pub status: u8,
}

impl Registers {

    pub fn new() -> Registers {
        Registers {
            accum: 0x00,
            x: 0x00,
            y: 0x00,
            stkp: 0x00,
            pc: 0x0000,
            status: 0x00,
        }
    }

}

pub struct CPU<'a> {
    pub bus: &'a mut Bus,

    pub flags: HashMap<Flags, u8>,
    pub reg: Registers,

    fetched: u8,        // Represents the working input value to the ALU
    temp: u16,          // A convenience variable used everywhere in the system
    addr_abs: u16,      // All used memory addresses end up in here
    addr_rel: u16,      // Represents absolute address following a branch
    op_code: u8,        // The instruction byte
    cycles: u8,         // Counts number of cycles the instruction has remaining
    clock_count: u32,   // A global accumulation of the number of clocks
}

impl<'a> CPU<'a> {

    pub fn new(bus: &mut Bus) -> CPU {
        CPU {
            bus,

            flags: HashMap::from([
                (Flags::C, (1 << 0)),    // Carry Bit
                (Flags::Z, (1 << 1)),    // Zero
                (Flags::I, (1 << 2)),    // Disable Interrupts
                (Flags::D, (1 << 3)),    // Decimal Mode
                (Flags::B, (1 << 4)),    // Break
                (Flags::U, (1 << 5)),    // Unused
                (Flags::V, (1 << 6)),    // Overflow
                (Flags::N, (1 << 7)),    // Negative
            ]),
            reg: Registers::new(),

            fetched: 0x00,
            temp: 0x0000,
            addr_abs: 0x0000,
            addr_rel: 0x00,
            op_code: 0x00,
            cycles: 0,
            clock_count: 0,
        }
    }

    pub fn complete(self) -> bool {
        self.cycles == 0
    }

    /// Perform one clock cycle's worth of emulation
    pub fn clock(&mut self) {
        if (self.cycles == 0) {
            // Read next instruction byte. This 8-bit value is used to index
            // the translation table to get the relevant information about how
            // to implement the instruction.
            self.op_code = self.read(self.reg.pc);

            // Always set the unused status flag bit to 1.
            self.set_flag(Flags::U, true);

            // Increment program counter, we read the opcode byte.
            self.reg.pc += 1;

            // Get starting number of cycles.
            self.cycles = CPU::lookup(self.op_code).c;

            // Perform fetch of intermediate data using the required
            // addressing mode.
            let additional_cycle_1 = (CPU::lookup(self.op_code).o)(self);

            // Perform operation
            let additional_cycle_2 = (CPU::lookup(self.op_code).o)(self);

            // The address mode and op_code may have altered the number
            // of cycles this instruction requires before it's completed.
            self.cycles += (additional_cycle_1 + additional_cycle_2);

            // Always set the unused status flag bit to 1.
            self.set_flag(Flags::U, true);

            // Increment the global clock count.
            self.clock_count += 1;

            // Decrement the number of cycles remaining for this instruction.
            self.cycles -= 1;
        }
    }

    fn write(&mut self, addr: u16, data: u8) {
        self.bus.cpu_write(addr, data);
    }

    fn read(&self, addr: u16) -> u8 {
        self.bus.cpu_read(addr)
    }

    fn get_flag(&mut self, flag: Flags) -> u8 {
        ((self.reg.status & self.flags[&flag]) > 0) as u8
    }

    fn set_flag(&mut self, flag: Flags, value: bool) {
        match value {
            true => self.reg.status |= self.flags[&flag],
            _ => self.reg.status &= !self.flags[&flag],
        };
    }

    /// This function sources the data used by the instruction into a
    /// convenient numeric variable. Some instructions don't have to fetch
    /// data as the source is implied by the instruction.
    ///
    /// For example, INX increments the X register. There is no additional
    /// data required. For all other addressing modes, the data resides at
    /// the location held within `addr_abs`, so it is read from there.
    ///
    /// Immediate address mode exploits this slightly, as that has set
    /// `addr_abs = pc + 1`, so it fetches the data from the next byte.
    ///
    /// For example, `LDA $FF` just loads the accumulator with 256, i.e. no
    /// far-reaching memory fetch is required.
    ///
    /// The variable `fetched` is global to the CPU, and it is set by calling
    /// this function. It also returns it for convenience.
    pub fn fetch(&mut self) -> u8 {

        if CPU::lookup(self.op_code).m != CPU::imp {
            self.fetched = self.read(self.addr_abs);
        }

        self.fetched
    }

    /// Forces the 6502 into a known state. This is hard-wired inside the CPU.
    /// The registers are set to 0x00, the status register is cleared except for
    /// unused bit, which remains at 1. An absolute address is read from location
    /// 0xFFFC which contains a second address that the program counter is set to.
    /// This allows the programmer to jump to a known and programmable location in
    /// the memory to start executing from. Typically the programmer would set the
    /// value at location 0xFFFC at compile time.
    pub fn reset(&mut self) {

        // Get address to set program counter to.
        self.addr_abs = 0xFFFC;
        let lo: u16 = self.read(self.addr_abs + 0) as u16;
        let hi: u16 = self.read(self.addr_abs + 1) as u16;

        // Set it.
        self.reg.pc = (hi << 8) | lo;

        // Reset internal registers.
        self.reg.accum = 0;
        self.reg.x = 0;
        self.reg.y = 0;
        self.reg.stkp = 0xFD;
        self.reg.status = 0x00 | Flags::U.bits();

        // Clear internal helper variables.
        self.addr_rel = 0x0000;
        self.addr_abs = 0x0000;
        self.fetched = 0x00;

        // Reset takes time.
        self.cycles = 8;
    }

    /// Interrupt requests are a complex operation and only happen if the
    /// "disable interrupt" flag is 0. IRQs can happen at any time, but you
    /// don't want them to be destructive to the operation of the running
    /// program. Therefore, teh current instruction is allowed to finish
    /// (facilitated by doing the whole thing when `cycles == 0`) and then
    /// the current program counter is stored on the stack.
    ///
    /// When the routine that services the interrupt has finished, the status
    /// register and program counter can be restored to how they were before
    /// it occurred. This is implemented by the RTI instruction.
    ///
    /// Once the IRQ has happened, in a similar way to a reset, a programmable
    /// address is read from hard-coded location 0xFFFE, which is subsequently
    /// set to the program counter.
    pub fn irq(&mut self) {

        // If interrupts are allowed
        if self.get_flag(Flags::I) == 0 {

            self.write(
                (0x0100 + self.reg.stkp) as u16,
                ((self.reg.pc >> 8) & 0x00FF) as u8,
            );
            self.reg.stkp -= 1;

            self.write(
                (0x0100 + self.reg.stkp) as u16,
                (self.reg.pc & 0x00FF) as u8,
            );
            self.reg.stkp -= 1;

            // Then push the status register to the stack.
            self.set_flag(Flags::B, false);
            self.set_flag(Flags::U, true);
            self.set_flag(Flags::I, true);
            self.write(0x0100 + self.reg.stkp as u16, self.reg.status);
            self.reg.stkp -= 1;

            // Read the new program counter location from fixed address
            self.addr_abs = 0xFFFE;
            let lo: u16 = self.read(self.addr_abs + 0) as u16;
            let hi: u16 = self.read(self.addr_abs + 1) as u16;
            self.reg.pc = (hi << 8) | lo;

            // IRQs take time
            self.cycles = 7;
        }
    }

    /// A Non-Maskable Interrupt cannot be ignored. It behaves in exactly the
    /// same way as a regular IRQ, but it reads the new program counter
    /// address from location 0xFFFA.
    pub fn nmi(&mut self) {
        self.write(
            (0x0100 + self.reg.stkp) as u16,
            ((self.reg.pc >> 8) & 0x00FF) as u8,
        );
        self.reg.stkp -= 1;

        self.write(
            (0x0100 + self.reg.stkp) as u16,
            (self.reg.pc & 0x00FF) as u8,
        );
        self.reg.stkp -= 1;

        self.set_flag(Flags::B, false);
        self.set_flag(Flags::U, true);
        self.set_flag(Flags::I, true);
        self.write(0x0100 + self.reg.stkp as u16, self.reg.status);
        self.reg.stkp -= 1;

        self.addr_abs = 0xFFFE;
        let lo: u16 = self.read(self.addr_abs + 0) as u16;
        let hi: u16 = self.read(self.addr_abs + 1) as u16;
        self.reg.pc = (hi << 8) | lo;

        self.cycles = 8;
    }
}

/// ADDRESSING MODES
impl<'a> CPU<'a> {

    /// Implied
    ///
    /// There is no additional data required for this instruction.
    /// The instruction does something very simple like sets a status bit.
    /// However, we will target the accumulator, for instructions like PHCPU::
    pub fn imp(&mut self) -> u8 {
        self.fetched = self.reg.accum;
        0
    }

    /// Immediate
    ///
    /// The instruction expects the next byte to be used as a value, so we'll
    /// prep the read address to point to the next byte.
    pub fn imm(&mut self) -> u8 {
        // Get the next byte
        self.reg.pc += 1;
        // Set the absolute address to the current program counter
        self.addr_abs = self.reg.pc;
        0
    }

    /// Zero-Page Addressing
    ///
    /// To save program bytes, zero-page addressing allows you to absolutely
    /// address a location in first 0xFF bytes of address range. Clearly this
    /// only requires one byte instead of the usual two.
    pub fn zp0(&mut self) -> u8 {
        self.addr_abs = self.read(self.reg.pc) as u16;
        0
    }

    /// Zero-Page Addressing with X Register Offset
    ///
    /// Fundamentally the same as zero-page addressing, but the contents of the
    /// X register is added to the supplied single byte address. This is useful
    /// for iterating through ranges within the first page.
    pub fn zpx(&mut self) -> u8 {
        self.addr_abs = self.read(
            self.reg.pc + self.reg.x as u16
        ) as u16;

        self.reg.pc += 1;
        self.addr_abs &= 0x00FF;
        0
    }

    /// Zero-Page Addressing with Y Register Offset
    ///
    /// Same as above but uses the Y register for offset.
    pub fn zpy(&mut self) -> u8 {
        self.addr_abs = self.read(
            self.reg.pc + self.reg.y as u16
        ) as u16;

        self.reg.pc += 1;
        self.addr_abs &= 0x00FF;
        0
    }

    /// Relative Addressing
    ///
    /// This address mode is exclusive to branch instructions. The address
    /// must reside within -128 to +127 of the branch instruction, i.e.
    /// you can't directly branch to any address in the addressable range.
    pub fn rel(&mut self) -> u8 {
        self.addr_rel = self.read(self.reg.pc) as u16;
        self.reg.pc += 1;

        if ((self.addr_rel & 0x80) != 0) {
            self.addr_rel |= 0xFF00;
        }

        0
    }

    /// Absolute Addressing
    ///
    /// A full 16-bit address is loaded and used.
    pub fn abs(&mut self) -> u8 {
        let lo: u16 = self.read(self.reg.pc) as u16;
        self.reg.pc += 1;

        let hi: u16 = self.read(self.reg.pc) as u16;
        self.reg.pc += 1;

        self.addr_abs = (hi << 8) | lo;
        0
    }

    /// Absolute Addressing with X Register Offset
    ///
    /// Fundamentally the same as absolute addressing, but the contents of the
    /// X register is added to the supplied two byte address. If the resulting
    /// address range changes the page, an additional clock cycle is required.
    pub fn abx(&mut self) -> u8 {
        let lo: u16 = self.read(self.reg.pc) as u16;
        self.reg.pc += 1;

        let hi: u16 = self.read(self.reg.pc) as u16;
        self.reg.pc += 1;

        self.addr_abs = (hi << 8) | lo;
        // X Register Offset
        self.addr_abs += self.reg.x as u16;

        // Return 1 (additional clock cycle) if page changed
        ((self.addr_abs & 0xFF00) != (hi << 8)) as u8
    }

    /// Absolute Addressing with Y Register Offset
    ///
    /// Fundamentally the same as absolute addressing, but the contents of the
    /// Y register is added to the supplied two byte address. If the resulting
    /// address range changes the page, an additional clock cycle is required.
    pub fn aby(&mut self) -> u8 {
        let lo: u16 = self.read(self.reg.pc) as u16;
        self.reg.pc += 1;

        let hi: u16 = self.read(self.reg.pc) as u16;
        self.reg.pc += 1;

        self.addr_abs = (hi << 8) | lo;
        // Y Register Offset
        self.addr_abs += self.reg.y as u16;

        // Return 1 (additional clock cycle) if page changed
        ((self.addr_abs & 0xFF00) != (hi << 8)) as u8
    }

    /// Indirect Addressing
    ///
    /// The supplied 16-bit address is read to get the actual 16-bit address.
    /// This instruction is unusual in that it has a bug in the hardware! To
    /// emulate its function accurately, we also need to emulate this bug. If
    /// the low byte of the supplied address is 0xFF, then to read the high
    /// byte of the actual address, we need to cross a page boundary. This
    /// doesn't actually work on the chip as designed; instead it wraps around
    /// in the same page, yielding an invalid actual address.
    pub fn ind(&mut self) -> u8 {

        let ptr_lo = self.read(self.reg.pc);
        self.reg.pc += 1;

        let ptr_hi = self.read(self.reg.pc);
        self.reg.pc += 1;

        let ptr = (ptr_hi << 8) | ptr_lo;

        if (ptr_lo == 0x00FF) {
            // Simulate page boundary hardware bug
            self.addr_abs =
                ((self.read(ptr as u16 & 0xFF00) << 8)
                | self.read(ptr as u16 + 0)) as u16;
        } else {
            // Behave normally
            self.addr_abs =
                ((self.read(ptr as u16 + 1) << 8)
                | self.read(ptr as u16 + 0)) as u16;
        }

        0
    }

    /// Indirect Addressing with X Register Offset
    ///
    /// The supplied 8-bit address is offset by X Register to index a location
    /// in page 0x00. The actual 16-bit address is read from this location.
    pub fn izx(&mut self) -> u8 {
        let t: u16 = self.read(self.reg.pc) as u16;
        self.reg.pc += 1;

        let lo: u16 = self.read((t + self.reg.x as u16) & 0x00FF) as u16;
        let hi: u16 = self.read((t + (self.reg.x + 1) as u16) & 0x00FF) as u16;

        self.addr_abs = (hi << 8) | lo;

        0
    }

    /// Indirect Addressing with Y Register Offset
    ///
    /// The supplied 8-bit address indexes a location in page 0x00. From here,
    /// the actual 16-bit address is read, and the contents of the Y Register
    /// is added to it to offset it. If the offset causes a change in page,
    /// then an additional clock cycle is required.
    pub fn izy(&mut self) -> u8 {
        let t: u16 = self.read(self.reg.pc) as u16;
        self.reg.pc += 1;

        let lo: u16 = self.read(t & 0x00FF) as u16;
        let hi: u16 = self.read((t + 1) & 0x00FF) as u16;

        self.addr_abs = (hi << 8) | lo;
        self.addr_abs += self.reg.y as u16;

        ((self.addr_abs & 0xFF00) != (hi << 8)) as u8
    }

}

/// OPCODES
impl<'a> CPU<'a> {

    /// Addition
    pub fn adc(&mut self) -> u8 {

        // Grab the data that we are adding to the accumulator.
        self.fetch();

        // Add is performed in the 16-bit domain for emulation to capture any
        // carry bit, which will exist in bit 8 of the 16-bit word.
        let temp: u16 = (
            self.reg.accum +
            self.fetched +
            self.get_flag(Flags::C)
        ) as u16;

        // The Carry flag out exists in the high byte bit 0.
        self.set_flag(Flags::C, temp > 255);

        // The Zero flag is set if the result is 0.
        self.set_flag(Flags::Z, (temp & 0x00FF) == 0);

        // The signed Overflow flag is set based on all that up there!
        self.set_flag(
            Flags::V,
            (
                !(self.reg.accum as u16 ^ self.fetched as u16) &
                (self.reg.accum as u16 ^ self.temp as u16) &
                0x0080
            ) != 0,
        );

        // The Negative flag is set to the most significant bit of the result.
        self.set_flag(Flags::N, (self.temp & 0x80) != 0);

        // Load the result into the accumulator (8-bit, don't forget!)
        self.reg.accum = (self.temp & 0x00FF) as u8;

        // This instruction has the potential to require an additional clock
        // cycle.
        1
    }

    /// Bitwise Logic AND
    ///
    /// `A = A & M` (OUT: N, Z)
    pub fn and(&mut self) -> u8 {
        self.fetch();
        self.reg.accum = self.reg.accum & self.fetched;

        self.set_flag(Flags::Z, self.reg.accum == 0x00);
        self.set_flag(Flags::N, (self.reg.accum & 0x80) != 0);

        1
    }

    /// Arithmetic Shift Left
    ///
    /// `A = C <- (A << 1) <- 0` (OUT: N, Z, C)
    pub fn asl(&mut self) -> u8 {
        self.fetch();
        self.temp = (self.fetched as u16) << 1;

        self.set_flag(Flags::C, (self.temp & 0xFF00) > 0);
        self.set_flag(Flags::Z, (self.temp & 0x00FF) == 0x00);
        self.set_flag(Flags::N, (self.temp & 0x80) != 0);

        if CPU::lookup(self.op_code).m == CPU::imp {
            self.reg.accum = (self.temp & 0x00FF) as u8;
        } else {
            self.write(self.addr_abs, (self.temp & 0x00FF) as u8);
        }

        0
    }

    /// Branch if Carry Clear
    ///
    /// `if (C == 0) pc = address`
    pub fn bcc(&mut self) -> u8 {
        if (self.get_flag(Flags::C) == 0) {
            self.cycles += 1;
            self.addr_abs = self.reg.pc + (self.addr_rel as u16);

            if ((self.addr_abs & 0xFF00) != (self.reg.pc & 0xFF00)) {
                self.cycles += 1;
            }

            self.reg.pc = self.addr_abs;
        }

        0
    }

    /// Branch if Carry Set
    ///
    /// `if (C == 1) pc = address`
    pub fn bcs(&mut self) -> u8 {
        if (self.get_flag(Flags::C) == 1) {
            self.cycles += 1;
            self.addr_abs = self.reg.pc + self.addr_rel;

            if (self.addr_abs & 0xFF00) != (self.reg.pc & 0xFF00) {
                self.cycles += 1;
            }

            self.reg.pc = self.addr_abs;
        }

        0
    }

    /// Branch if Equal
    ///
    /// `if (Z == 1) pc = address`
    pub fn beq(&mut self) -> u8 {
        if (self.get_flag(Flags::Z) == 1) {
            self.cycles += 1;
            self.addr_abs = self.reg.pc + self.addr_rel;

            if (self.addr_abs & 0xFF00) != (self.reg.pc & 0xFF00) {
                self.cycles += 1;
            }

            self.reg.pc = self.addr_abs;
        }

        0
    }

    pub fn bit(&mut self) -> u8 {
        self.fetch();

        self.temp = (self.reg.accum & self.fetched) as u16;
        self.set_flag(Flags::Z, (self.temp & 0xFF00) == 0x00);
        self.set_flag(Flags::N, (self.fetched & (1 << 7)) != 0);
        self.set_flag(Flags::V, (self.fetched & (1 << 6)) != 0);

        0
    }

    /// Branch if Negative
    ///
    /// `if (N == 1) pc = address`
    pub fn bmi(&mut self) -> u8 {
        if self.get_flag(Flags::N) == 1 {
            self.cycles += 1;
            self.addr_abs = self.reg.pc + self.addr_rel;

            if (self.addr_abs & 0xFF00) != (self.reg.pc & 0xFF00) {
                self.cycles += 1;
            }

            self.reg.pc = self.addr_abs;
        }

        0
    }

    /// Branch if Not Equal
    ///
    /// `if (Z == 0) pc = address`
    pub fn bne(&mut self) -> u8 {
        if self.get_flag(Flags::Z) == 0 {
            self.cycles += 1;
            self.addr_abs = self.reg.pc + self.addr_rel;

            if (self.addr_abs & 0xFF00) != (self.reg.pc & 0xFF00) {
                self.cycles += 1;
            }

            self.reg.pc = self.addr_abs;
        }

        0
    }

    /// Branch if Positive
    ///
    /// `if (N == 0) pc = address`
    pub fn bpl(&mut self) -> u8 {
        if self.get_flag(Flags::N) == 0 {
            self.cycles += 1;
            self.addr_abs = self.reg.pc + self.addr_rel;

            if (self.addr_abs & 0xFF00) != (self.reg.pc & 0xFF00) {
                self.cycles += 1;
            }

            self.reg.pc = self.addr_abs;
        }

        0
    }

    /// Break
    ///
    /// Program Sourced Interrupt
    pub fn brk(&mut self) -> u8 {
        self.reg.pc += 1;

        self.set_flag(Flags::I, true);
        self.write(
            (0x0100 + self.reg.stkp) as u16,
            ((self.reg.pc >> 8) & 0x00FF) as u8,
        );
        self.reg.stkp -= 1;

        self.write(
            (0x0100 + self.reg.stkp) as u16,
            (self.reg.pc & 0x00FF) as u8,
        );
        self.reg.stkp -= 1;

        self.set_flag(Flags::B, true);
        self.write(
            (0x0100 + self.reg.stkp) as u16,
            self.reg.status,
        );

        0
    }

    /// Branch if Overflow Clear
    ///
    /// `if (V == 0) pc = address`
    pub fn bvc(&mut self) -> u8 {
        if self.get_flag(Flags::V) == 0 {
            self.cycles += 1;
            self.addr_abs = self.reg.pc + self.addr_rel;

            if (self.addr_abs & 0xFF00) != (self.reg.pc & 0xFF00) {
                self.cycles += 1;
            }

            self.reg.pc = self.addr_abs;
        }

        0
    }

    /// Branch if Overflow Set
    ///
    /// `if (V == 1) pc = address`
    pub fn bvs(&mut self) -> u8 {
        if self.get_flag(Flags::V) == 1 {
            self.cycles += 1;
            self.addr_abs = self.reg.pc + self.addr_rel;

            if (self.addr_abs & 0xFF00) != (self.reg.pc & 0xFF00) {
                self.cycles += 1;
            }

            self.reg.pc = self.addr_abs;
        }

        0
    }

    /// Clear Carry Flag
    pub fn clc(&mut self) -> u8 {
        self.set_flag(Flags::C, false);
        0
    }

    /// Clear Decimal Flag
    pub fn cld(&mut self) -> u8 {
        self.set_flag(Flags::D, false);
        0
    }

    /// Clear Interrupt Flag
    pub fn cli(&mut self) -> u8 {
        self.set_flag(Flags::I, false);
        0
    }

    /// Clear Overflow Flag
    pub fn clv(&mut self) -> u8 {
        self.set_flag(Flags::V, false);
        0
    }

    /// Compare Accumulator
    ///
    /// `C <- A >= M ; Z <- (A - M) == 0` (Out: N, C, Z)
    pub fn cmp(&mut self) -> u8 {
        self.fetch();
        self.temp = (self.reg.accum - self.fetched) as u16;
        self.set_flag(Flags::C, self.reg.accum > self.fetched);
        self.set_flag(Flags::Z, (self.temp & 0x00FF) == 0x0000);
        self.set_flag(Flags::N, (self.temp & 0x0080) != 0);
        1
    }

    pub fn cpx(&mut self) -> u8 {
        0
    }

    pub fn cpy(&mut self) -> u8 {
        0
    }

    pub fn dec(&mut self) -> u8 {
        0
    }

    pub fn dex(&mut self) -> u8 {
        0
    }

    pub fn dey(&mut self) -> u8 {
        0
    }

    pub fn eor(&mut self) -> u8 {
        0
    }

    pub fn inc(&mut self) -> u8 {
        0
    }

    pub fn inx(&mut self) -> u8 {
        0
    }

    pub fn iny(&mut self) -> u8 {
        0
    }

    pub fn jmp(&mut self) -> u8 {
        0
    }

    pub fn jsr(&mut self) -> u8 {
        0
    }

    pub fn lda(&mut self) -> u8 {
        0
    }

    pub fn ldx(&mut self) -> u8 {
        0
    }

    pub fn ldy(&mut self) -> u8 {
        0
    }

    pub fn lsr(&mut self) -> u8 {
        0
    }

    pub fn nop(&mut self) -> u8 {
        0
    }

    pub fn ora(&mut self) -> u8 {
        0
    }

    pub fn pha(&mut self) -> u8 {
        0
    }

    pub fn php(&mut self) -> u8 {
        0
    }

    pub fn pla(&mut self) -> u8 {
        0
    }

    pub fn plp(&mut self) -> u8 {
        0
    }

    pub fn rol(&mut self) -> u8 {
        self.fetch();
        self.temp = ((self.fetched << 1) | self.get_flag(Flags::C)) as u16;
        self.set_flag(Flags::C, (self.temp & 0xFF00) != 0);
        self.set_flag(Flags::Z, (self.temp & 0x00FF) == 0x0000);
        self.set_flag(Flags::N, (self.temp & 0x0080) != 0);

        if CPU::lookup(self.op_code).m == CPU::imp {
            self.reg.accum = (self.temp & 0x00FF) as u8;
        } else {
            self.write(self.addr_abs, (self.temp & 0x00Ff) as u8);
        }

        0
    }

    pub fn ror(&mut self) -> u8 {
        0
    }

    pub fn rti(&mut self) -> u8 {
        0
    }

    pub fn rts(&mut self) -> u8 {
        0
    }

    pub fn sbc(&mut self) -> u8 {
        0
    }

    pub fn sec(&mut self) -> u8 {
        0
    }

    pub fn sed(&mut self) -> u8 {
        0
    }

    pub fn sei(&mut self) -> u8 {
        0
    }

    pub fn sta(&mut self) -> u8 {
        0
    }

    pub fn stx(&mut self) -> u8 {
        0
    }

    pub fn sty(&mut self) -> u8 {
        0
    }

    pub fn tax(&mut self) -> u8 {
        0
    }

    pub fn tay(&mut self) -> u8 {
        0
    }

    pub fn tsx(&mut self) -> u8 {
        0
    }

    pub fn txa(&mut self) -> u8 {
        0
    }

    pub fn txs(&mut self) -> u8 {
        0
    }

    pub fn tya(&mut self) -> u8 {
        0
    }

    pub fn xxx(&mut self) -> u8 {
        0
    }
}

/// Lookup Table
impl<'a> CPU<'a> {

    pub fn lookup(op_code: u8) -> Instruction<'a> {

        let table: [Instruction; 256] = [
            Instruction { n: "BRK", o: CPU::brk, m: CPU::imm, c: 7 },
            Instruction { n: "ORA", o: CPU::ora, m: CPU::izx, c: 6 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 2 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 8 },
            Instruction { n: "???", o: CPU::nop, m: CPU::imp, c: 3 },
            Instruction { n: "ORA", o: CPU::ora, m: CPU::zp0, c: 3 },
            Instruction { n: "ASL", o: CPU::asl, m: CPU::zp0, c: 5 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 5 },
            Instruction { n: "PHP", o: CPU::php, m: CPU::imp, c: 3 },
            Instruction { n: "ORA", o: CPU::ora, m: CPU::imm, c: 2 },
            Instruction { n: "ASL", o: CPU::asl, m: CPU::imp, c: 2 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 2 },
            Instruction { n: "???", o: CPU::nop, m: CPU::imp, c: 4 },
            Instruction { n: "ORA", o: CPU::ora, m: CPU::abs, c: 4 },
            Instruction { n: "ASL", o: CPU::asl, m: CPU::abs, c: 6 },

            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 6 },
            Instruction { n: "BPL", o: CPU::bpl, m: CPU::rel, c: 2 },
            Instruction { n: "ORA", o: CPU::ora, m: CPU::izy, c: 5 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 2 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 8 },
            Instruction { n: "???", o: CPU::nop, m: CPU::imp, c: 4 },
            Instruction { n: "ORA", o: CPU::ora, m: CPU::zpx, c: 4 },
            Instruction { n: "ASL", o: CPU::asl, m: CPU::zpx, c: 6 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 6 },
            Instruction { n: "CLC", o: CPU::clc, m: CPU::imp, c: 2 },
            Instruction { n: "ORA", o: CPU::ora, m: CPU::aby, c: 4 },
            Instruction { n: "???", o: CPU::nop, m: CPU::imp, c: 2 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 7 },
            Instruction { n: "???", o: CPU::nop, m: CPU::imp, c: 4 },
            Instruction { n: "ORA", o: CPU::ora, m: CPU::abx, c: 4 },
            Instruction { n: "ASL", o: CPU::asl, m: CPU::abx, c: 7 },

            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 7 },
            Instruction { n: "JSR", o: CPU::jsr, m: CPU::abs, c: 6 },
            Instruction { n: "AND", o: CPU::and, m: CPU::izx, c: 6 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 2 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 8 },
            Instruction { n: "BIT", o: CPU::bit, m: CPU::zp0, c: 3 },
            Instruction { n: "AND", o: CPU::and, m: CPU::zp0, c: 3 },
            Instruction { n: "ROL", o: CPU::rol, m: CPU::zp0, c: 5 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 5 },
            Instruction { n: "PLP", o: CPU::plp, m: CPU::imp, c: 4 },
            Instruction { n: "AND", o: CPU::and, m: CPU::imm, c: 2 },
            Instruction { n: "ROL", o: CPU::rol, m: CPU::imp, c: 2 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 2 },
            Instruction { n: "BIT", o: CPU::bit, m: CPU::abs, c: 4 },
            Instruction { n: "AND", o: CPU::and, m: CPU::abs, c: 4 },
            Instruction { n: "ROL", o: CPU::rol, m: CPU::abs, c: 6 },

            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 6 },
            Instruction { n: "BMI", o: CPU::bmi, m: CPU::rel, c: 2 },
            Instruction { n: "AND", o: CPU::and, m: CPU::izy, c: 5 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 2 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 8 },
            Instruction { n: "???", o: CPU::nop, m: CPU::imp, c: 4 },
            Instruction { n: "AND", o: CPU::and, m: CPU::zpx, c: 4 },
            Instruction { n: "ROL", o: CPU::rol, m: CPU::zpx, c: 6 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 6 },
            Instruction { n: "SEC", o: CPU::sec, m: CPU::imp, c: 2 },
            Instruction { n: "AND", o: CPU::and, m: CPU::aby, c: 4 },
            Instruction { n: "???", o: CPU::nop, m: CPU::imp, c: 2 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 7 },
            Instruction { n: "???", o: CPU::nop, m: CPU::imp, c: 4 },
            Instruction { n: "AND", o: CPU::and, m: CPU::abx, c: 4 },
            Instruction { n: "ROL", o: CPU::rol, m: CPU::abx, c: 7 },

            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 7 },
            Instruction { n: "RTI", o: CPU::rti, m: CPU::imp, c: 6 },
            Instruction { n: "EOR", o: CPU::eor, m: CPU::izx, c: 6 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 2 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 8 },
            Instruction { n: "???", o: CPU::nop, m: CPU::imp, c: 3 },
            Instruction { n: "EOR", o: CPU::eor, m: CPU::zp0, c: 3 },
            Instruction { n: "LSR", o: CPU::lsr, m: CPU::zp0, c: 5 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 5 },
            Instruction { n: "PHA", o: CPU::pha, m: CPU::imp, c: 3 },
            Instruction { n: "EOR", o: CPU::eor, m: CPU::imm, c: 2 },
            Instruction { n: "LSR", o: CPU::lsr, m: CPU::imp, c: 2 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 2 },
            Instruction { n: "JMP", o: CPU::jmp, m: CPU::abs, c: 3 },
            Instruction { n: "EOR", o: CPU::eor, m: CPU::abs, c: 4 },
            Instruction { n: "LSR", o: CPU::lsr, m: CPU::abs, c: 6 },

            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 6 },
            Instruction { n: "BVC", o: CPU::bvc, m: CPU::rel, c: 2 },
            Instruction { n: "EOR", o: CPU::eor, m: CPU::izy, c: 5 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 2 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 8 },
            Instruction { n: "???", o: CPU::nop, m: CPU::imp, c: 4 },
            Instruction { n: "EOR", o: CPU::eor, m: CPU::zpx, c: 4 },
            Instruction { n: "LSR", o: CPU::lsr, m: CPU::zpx, c: 6 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 6 },
            Instruction { n: "CLI", o: CPU::cli, m: CPU::imp, c: 2 },
            Instruction { n: "EOR", o: CPU::eor, m: CPU::aby, c: 4 },
            Instruction { n: "???", o: CPU::nop, m: CPU::imp, c: 2 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 7 },
            Instruction { n: "???", o: CPU::nop, m: CPU::imp, c: 4 },
            Instruction { n: "EOR", o: CPU::eor, m: CPU::abx, c: 4 },
            Instruction { n: "LSR", o: CPU::lsr, m: CPU::abx, c: 7 },

            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 7 },
            Instruction { n: "RTS", o: CPU::rts, m: CPU::imp, c: 6 },
            Instruction { n: "ADC", o: CPU::adc, m: CPU::izx, c: 6 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 2 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 8 },
            Instruction { n: "???", o: CPU::nop, m: CPU::imp, c: 3 },
            Instruction { n: "ADC", o: CPU::adc, m: CPU::zp0, c: 3 },
            Instruction { n: "ROR", o: CPU::ror, m: CPU::zp0, c: 5 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 5 },
            Instruction { n: "PLA", o: CPU::pla, m: CPU::imp, c: 4 },
            Instruction { n: "ADC", o: CPU::adc, m: CPU::imm, c: 2 },
            Instruction { n: "ROR", o: CPU::ror, m: CPU::imp, c: 2 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 2 },
            Instruction { n: "JMP", o: CPU::jmp, m: CPU::ind, c: 5 },
            Instruction { n: "ADC", o: CPU::adc, m: CPU::abs, c: 4 },
            Instruction { n: "ROR", o: CPU::ror, m: CPU::abs, c: 6 },

            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 6 },
            Instruction { n: "BVS", o: CPU::bvs, m: CPU::rel, c: 2 },
            Instruction { n: "ADC", o: CPU::adc, m: CPU::izy, c: 5 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 2 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 8 },
            Instruction { n: "???", o: CPU::nop, m: CPU::imp, c: 4 },
            Instruction { n: "ADC", o: CPU::adc, m: CPU::zpx, c: 4 },
            Instruction { n: "ROR", o: CPU::ror, m: CPU::zpx, c: 6 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 6 },
            Instruction { n: "SEI", o: CPU::sei, m: CPU::imp, c: 2 },
            Instruction { n: "ADC", o: CPU::adc, m: CPU::aby, c: 4 },
            Instruction { n: "???", o: CPU::nop, m: CPU::imp, c: 2 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 7 },
            Instruction { n: "???", o: CPU::nop, m: CPU::imp, c: 4 },
            Instruction { n: "ADC", o: CPU::adc, m: CPU::abx, c: 4 },
            Instruction { n: "ROR", o: CPU::ror, m: CPU::abx, c: 7 },

            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 7 },
            Instruction { n: "???", o: CPU::nop, m: CPU::imp, c: 2 },
            Instruction { n: "STA", o: CPU::sta, m: CPU::izx, c: 6 },
            Instruction { n: "???", o: CPU::nop, m: CPU::imp, c: 2 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 6 },
            Instruction { n: "STY", o: CPU::sty, m: CPU::zp0, c: 3 },
            Instruction { n: "STA", o: CPU::sta, m: CPU::zp0, c: 3 },
            Instruction { n: "STX", o: CPU::stx, m: CPU::zp0, c: 3 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 3 },
            Instruction { n: "DEY", o: CPU::dey, m: CPU::imp, c: 2 },
            Instruction { n: "???", o: CPU::nop, m: CPU::imp, c: 2 },
            Instruction { n: "TXA", o: CPU::txa, m: CPU::imp, c: 2 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 2 },
            Instruction { n: "STY", o: CPU::sty, m: CPU::abs, c: 4 },
            Instruction { n: "STA", o: CPU::sta, m: CPU::abs, c: 4 },
            Instruction { n: "STX", o: CPU::stx, m: CPU::abs, c: 4 },

            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 4 },
            Instruction { n: "BCC", o: CPU::bcc, m: CPU::rel, c: 2 },
            Instruction { n: "STA", o: CPU::sta, m: CPU::izy, c: 6 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 2 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 6 },
            Instruction { n: "STY", o: CPU::sty, m: CPU::zpx, c: 4 },
            Instruction { n: "STA", o: CPU::sta, m: CPU::zpx, c: 4 },
            Instruction { n: "STX", o: CPU::stx, m: CPU::zpy, c: 4 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 4 },
            Instruction { n: "TYA", o: CPU::tya, m: CPU::imp, c: 2 },
            Instruction { n: "STA", o: CPU::sta, m: CPU::aby, c: 5 },
            Instruction { n: "TXS", o: CPU::txs, m: CPU::imp, c: 2 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 5 },
            Instruction { n: "???", o: CPU::nop, m: CPU::imp, c: 5 },
            Instruction { n: "STA", o: CPU::sta, m: CPU::abx, c: 5 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 5 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 5 },

            Instruction { n: "LDY", o: CPU::ldy, m: CPU::imm, c: 2 },
            Instruction { n: "LDA", o: CPU::lda, m: CPU::izx, c: 6 },
            Instruction { n: "LDX", o: CPU::ldx, m: CPU::imm, c: 2 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 6 },
            Instruction { n: "LDY", o: CPU::ldy, m: CPU::zp0, c: 3 },
            Instruction { n: "LDA", o: CPU::lda, m: CPU::zp0, c: 3 },
            Instruction { n: "LDX", o: CPU::ldx, m: CPU::zp0, c: 3 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 3 },
            Instruction { n: "TAY", o: CPU::tay, m: CPU::imp, c: 2 },
            Instruction { n: "LDA", o: CPU::lda, m: CPU::imm, c: 2 },
            Instruction { n: "TAX", o: CPU::tax, m: CPU::imp, c: 2 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 2 },
            Instruction { n: "LDY", o: CPU::ldy, m: CPU::abs, c: 4 },
            Instruction { n: "LDA", o: CPU::lda, m: CPU::abs, c: 4 },
            Instruction { n: "LDX", o: CPU::ldx, m: CPU::abs, c: 4 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 4 },

            Instruction { n: "BCS", o: CPU::bcs, m: CPU::rel, c: 2 },
            Instruction { n: "LDA", o: CPU::lda, m: CPU::izy, c: 5 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 2 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 5 },
            Instruction { n: "LDY", o: CPU::ldy, m: CPU::zpx, c: 4 },
            Instruction { n: "LDA", o: CPU::lda, m: CPU::zpx, c: 4 },
            Instruction { n: "LDX", o: CPU::ldx, m: CPU::zpy, c: 4 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 4 },
            Instruction { n: "CLV", o: CPU::clv, m: CPU::imp, c: 2 },
            Instruction { n: "LDA", o: CPU::lda, m: CPU::aby, c: 4 },
            Instruction { n: "TSX", o: CPU::tsx, m: CPU::imp, c: 2 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 4 },
            Instruction { n: "LDY", o: CPU::ldy, m: CPU::abx, c: 4 },
            Instruction { n: "LDA", o: CPU::lda, m: CPU::abx, c: 4 },
            Instruction { n: "LDX", o: CPU::ldx, m: CPU::aby, c: 4 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 4 },

            Instruction { n: "CPY", o: CPU::cpy, m: CPU::imm, c: 2 },
            Instruction { n: "CMP", o: CPU::cmp, m: CPU::izx, c: 6 },
            Instruction { n: "???", o: CPU::nop, m: CPU::imp, c: 2 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 8 },
            Instruction { n: "CPY", o: CPU::cpy, m: CPU::zp0, c: 3 },
            Instruction { n: "CMP", o: CPU::cmp, m: CPU::zp0, c: 3 },
            Instruction { n: "DEC", o: CPU::dec, m: CPU::zp0, c: 5 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 5 },
            Instruction { n: "INY", o: CPU::iny, m: CPU::imp, c: 2 },
            Instruction { n: "CMP", o: CPU::cmp, m: CPU::imm, c: 2 },
            Instruction { n: "DEX", o: CPU::dex, m: CPU::imp, c: 2 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 2 },
            Instruction { n: "CPY", o: CPU::cpy, m: CPU::abs, c: 4 },
            Instruction { n: "CMP", o: CPU::cmp, m: CPU::abs, c: 4 },
            Instruction { n: "DEC", o: CPU::dec, m: CPU::abs, c: 6 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 6 },

            Instruction { n: "BNE", o: CPU::bne, m: CPU::rel, c: 2 },
            Instruction { n: "CMP", o: CPU::cmp, m: CPU::izy, c: 5 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 2 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 8 },
            Instruction { n: "???", o: CPU::nop, m: CPU::imp, c: 4 },
            Instruction { n: "CMP", o: CPU::cmp, m: CPU::zpx, c: 4 },
            Instruction { n: "DEC", o: CPU::dec, m: CPU::zpx, c: 6 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 6 },
            Instruction { n: "CLD", o: CPU::cld, m: CPU::imp, c: 2 },
            Instruction { n: "CMP", o: CPU::cmp, m: CPU::aby, c: 4 },
            Instruction { n: "NOP", o: CPU::nop, m: CPU::imp, c: 2 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 7 },
            Instruction { n: "???", o: CPU::nop, m: CPU::imp, c: 4 },
            Instruction { n: "CMP", o: CPU::cmp, m: CPU::abx, c: 4 },
            Instruction { n: "DEC", o: CPU::dec, m: CPU::abx, c: 7 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 7 },

            Instruction { n: "CPX", o: CPU::cpx, m: CPU::imm, c: 2 },
            Instruction { n: "SBC", o: CPU::sbc, m: CPU::izx, c: 6 },
            Instruction { n: "???", o: CPU::nop, m: CPU::imp, c: 2 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 8 },
            Instruction { n: "CPX", o: CPU::cpx, m: CPU::zp0, c: 3 },
            Instruction { n: "SBC", o: CPU::sbc, m: CPU::zp0, c: 3 },
            Instruction { n: "INC", o: CPU::inc, m: CPU::zp0, c: 5 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 5 },
            Instruction { n: "INX", o: CPU::inx, m: CPU::imp, c: 2 },
            Instruction { n: "SBC", o: CPU::sbc, m: CPU::imm, c: 2 },
            Instruction { n: "NOP", o: CPU::nop, m: CPU::imp, c: 2 },
            Instruction { n: "???", o: CPU::sbc, m: CPU::imp, c: 2 },
            Instruction { n: "CPX", o: CPU::cpx, m: CPU::abs, c: 4 },
            Instruction { n: "SBC", o: CPU::sbc, m: CPU::abs, c: 4 },
            Instruction { n: "INC", o: CPU::inc, m: CPU::abs, c: 6 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 6 },

            Instruction { n: "BEQ", o: CPU::beq, m: CPU::rel, c: 2 },
            Instruction { n: "SBC", o: CPU::sbc, m: CPU::izy, c: 5 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 2 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 8 },
            Instruction { n: "???", o: CPU::nop, m: CPU::imp, c: 4 },
            Instruction { n: "SBC", o: CPU::sbc, m: CPU::zpx, c: 4 },
            Instruction { n: "INC", o: CPU::inc, m: CPU::zpx, c: 6 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 6 },
            Instruction { n: "SED", o: CPU::sed, m: CPU::imp, c: 2 },
            Instruction { n: "SBC", o: CPU::sbc, m: CPU::aby, c: 4 },
            Instruction { n: "NOP", o: CPU::nop, m: CPU::imp, c: 2 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 7 },
            Instruction { n: "???", o: CPU::nop, m: CPU::imp, c: 4 },
            Instruction { n: "SBC", o: CPU::sbc, m: CPU::abx, c: 4 },
            Instruction { n: "INC", o: CPU::inc, m: CPU::abx, c: 7 },
            Instruction { n: "???", o: CPU::xxx, m: CPU::imp, c: 7 },
        ];

        table[op_code as usize]
    }
}
