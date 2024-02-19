
pub struct Memory(Vec<u8>);


impl Memory {

    pub fn new() -> Memory {
        Memory(vec![0x00; 2048])
    }

    pub fn read(&self, addr: u16) -> u8 {
        self.0[(addr & 0x07FF) as usize]
    }

    pub fn write(&mut self, addr: u16, data: u8) {
        if addr <= 0x1FFF {
            self.0[(addr & 0x07FF) as usize] = data;
        }
    }

}
