// rewrite necessary contents from fancy_garbling to accelerate circuit execution

pub mod gb;
pub mod ev;
#[allow(non_snake_case)]
pub mod inner_gb;
#[allow(non_snake_case)]
pub mod inner_ev;
pub mod traits;
#[allow(non_snake_case)]
pub mod util;
pub mod binary;

macro_rules! check_binary {
    ($x:ident) => {
        if $x.modulus() != 2 {
            return Err(Self::Error::from(FancyError::InvalidArgMod {
                got: $x.modulus(),
                needed: 2,
            }));
        }
    };
}

pub(crate) use check_binary;



