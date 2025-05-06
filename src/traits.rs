pub trait FromPrimitive {
    fn from(n: usize) -> Self;
}

impl FromPrimitive for u32 {
    fn from(n: usize) -> Self {
        n as u32
    }
}

impl FromPrimitive for u64 {
    fn from(n: usize) -> Self {
        n as u64
    }
}

impl FromPrimitive for u128 {
    fn from(n: usize) -> Self {
        n as u128
    }
}
