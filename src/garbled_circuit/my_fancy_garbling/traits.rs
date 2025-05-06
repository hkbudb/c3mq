use fancy_garbling::{FancyError, HasModulus};
use itertools::Itertools;
use rayon::{iter::{IntoParallelRefIterator, ParallelIterator}, slice::ParallelSlice, ThreadPoolBuilder};
use std::ops::{Deref, DerefMut};
use super::util;
use std::ops::Index;

/// Convenience functions for encoding input to Fancy objects.
pub trait FancyInput {
    /// The type that this Fancy object operates over.
    type Item: Clone + HasModulus + Send + Sync;

    /// The type of error that this Fancy object emits.
    type Error: From<FancyError>;

    ////////////////////////////////////////////////////////////////////////////////
    // required methods

    /// Encode many values where the actual input is known.
    ///
    /// When writing a garbler, the return value must correspond to the zero
    /// wire label.
    fn encode_many(
        &mut self,
        values: &[u16],
        moduli: &[u16],
    ) -> Result<Vec<Self::Item>, Self::Error>;

    /// Receive many values where the input is not known.
    fn receive_many(&mut self, moduli: &[u16]) -> Result<Vec<Self::Item>, Self::Error>;

    ////////////////////////////////////////////////////////////////////////////////
    // optional methods

    /// Encode a single value.
    ///
    /// When writing a garbler, the return value must correspond to the zero
    /// wire label.
    fn encode(&mut self, value: u16, modulus: u16) -> Result<Self::Item, Self::Error> {
        let mut xs = self.encode_many(&[value], &[modulus])?;
        Ok(xs.remove(0))
    }

    /// Receive a single value.
    fn receive(&mut self, modulus: u16) -> Result<Self::Item, Self::Error> {
        let mut xs = self.receive_many(&[modulus])?;
        Ok(xs.remove(0))
    }

    /// Encode a bundle.
    fn encode_bundle(
        &mut self,
        values: &[u16],
        moduli: &[u16],
    ) -> Result<Bundle<Self::Item>, Self::Error> {
        self.encode_many(values, moduli).map(Bundle::new)
    }

    /// Receive a bundle.
    fn receive_bundle(&mut self, moduli: &[u16]) -> Result<Bundle<Self::Item>, Self::Error> {
        self.receive_many(moduli).map(Bundle::new)
    }

    /// Encode many input bundles.
    fn encode_bundles(
        &mut self,
        values: &[Vec<u16>],
        moduli: &[Vec<u16>],
    ) -> Result<Vec<Bundle<Self::Item>>, Self::Error> {
        println!("encode_bundles");
        let qs = moduli.iter().flatten().cloned().collect_vec();
        let xs = values.iter().flatten().cloned().collect_vec();
        if xs.len() != qs.len() {
            return Err(
                FancyError::InvalidArg("unequal number of values and moduli".to_string()).into(),
            );
        }
        let mut wires = self.encode_many(&xs, &qs)?;
        let buns = moduli
            .iter()
            .map(|qs| {
                let ws = wires.drain(0..qs.len()).collect_vec();
                Bundle::new(ws)
            })
            .collect_vec();
        Ok(buns)
    }

    /// Receive many input bundles.
    fn receive_many_bundles(
        &mut self,
        moduli: &[Vec<u16>],
    ) -> Result<Vec<Bundle<Self::Item>>, Self::Error> {
        println!("receive_many_bundles");
        let qs = moduli.iter().flatten().cloned().collect_vec();
        let mut wires = self.receive_many(&qs)?;
        let buns = moduli
            .iter()
            .map(|qs| {
                let ws = wires.drain(0..qs.len()).collect_vec();
                Bundle::new(ws)
            })
            .collect_vec();
        Ok(buns)
    }

    /// Encode a binary input bundle.
    fn bin_encode(
        &mut self,
        value: u128,
        nbits: usize,
    ) -> Result<BinaryBundle<Self::Item>, Self::Error> {
        let xs = util::u128_to_bits(value, nbits);
        self.encode_bundle(&xs, &vec![2; nbits])
            .map(BinaryBundle::from)
    }

    /// Receive an binary input bundle.
    fn bin_receive(&mut self, nbits: usize) -> Result<BinaryBundle<Self::Item>, Self::Error> {
        self.receive_bundle(&vec![2; nbits]).map(BinaryBundle::from)
    }

    /// Encode many binary input bundles.
    fn bin_encode_many(
        &mut self,
        values: &[u128],
        nbits: usize,
    ) -> Result<Vec<BinaryBundle<Self::Item>>, Self::Error> 
    {
        let pool1 = ThreadPoolBuilder::new().num_threads(4).build().unwrap();
        let xs: Vec<u16> = pool1.install(|| {
            values.par_iter().flat_map(|x| util::u128_to_bits(*x, nbits)).collect()
        });

        let wires = self.encode_many(&xs, &vec![2; values.len() * nbits])?;

        let pool2 = ThreadPoolBuilder::new().num_threads(4).build().unwrap();
        let buns: Vec<BinaryBundle<Self::Item>> = pool2.install(|| {
            wires.par_chunks(nbits).map(|ws| BinaryBundle::new(ws.to_vec())).collect()
        });
        
        Ok(buns)
    }

    /// Receive many binary input bundles.
    fn bin_receive_many(
        &mut self,
        ninputs: usize,
        nbits: usize,
    ) -> Result<Vec<BinaryBundle<Self::Item>>, Self::Error> {
        let wires = self.receive_many(&vec![2; ninputs * nbits])?;
        
        let pool = ThreadPoolBuilder::new().num_threads(4).build().unwrap();

        let buns: Vec<BinaryBundle<Self::Item>> = pool.install(|| {
            wires.par_chunks(nbits).map(|ws| BinaryBundle::new(ws.to_vec())).collect()
        });
        
        Ok(buns)
    }
}


pub trait FancyBinary: Fancy {
    /// Binary Xor
    fn xor(&self, x: &Self::Item, y: &Self::Item) -> Result<Self::Item, Self::Error>;

    /// Binary And
    fn and(&mut self, x: &Self::Item, y: &Self::Item) -> Result<Self::Item, Self::Error>;

    /// Binary Not
    fn negate(&self, x: &Self::Item) -> Result<Self::Item, Self::Error>;

    /// Uses Demorgan's Rule implemented with an and gate and negation.
    fn or(&mut self, x: &Self::Item, y: &Self::Item) -> Result<Self::Item, Self::Error> {
        let notx = self.negate(x)?;
        let noty = self.negate(y)?;
        let z = self.and(&notx, &noty)?;
        self.negate(&z)
    }

    /// Binary adder. Returns the result and the carry.
    fn adder(
        &mut self,
        x: &Self::Item,
        y: &Self::Item,
        carry_in: Option<&Self::Item>,
    ) -> Result<(Self::Item, Self::Item), Self::Error> {
        if let Some(c) = carry_in {
            let z1 = self.xor(x, y)?;
            let z2 = self.xor(&z1, c)?;
            let z3 = self.xor(x, c)?;
            let z4 = self.and(&z1, &z3)?;
            let carry = self.xor(&z4, x)?;
            Ok((z2, carry))
        } else {
            let z = self.xor(x, y)?;
            let carry = self.and(x, y)?;
            Ok((z, carry))
        }
    }
    /// Returns 1 if all wires equal 1.
    fn and_many(&mut self, args: &[Self::Item]) -> Result<Self::Item, Self::Error> {
        if args.is_empty() {
            return Err(Self::Error::from(FancyError::InvalidArgNum {
                got: args.len(),
                needed: 1,
            }));
        }
        args.iter()
            .skip(1)
            .fold(Ok(args[0].clone()), |acc, x| self.and(&(acc?), x))
    }

    /// Returns 1 if any wire equals 1.
    fn or_many(&mut self, args: &[Self::Item]) -> Result<Self::Item, Self::Error> {
        if args.is_empty() {
            return Err(Self::Error::from(FancyError::InvalidArgNum {
                got: args.len(),
                needed: 1,
            }));
        }
        args.iter()
            .skip(1)
            .fold(Ok(args[0].clone()), |acc, x| self.or(&(acc?), x))
    }

    /// XOR many wires together
    fn xor_many(&mut self, args: &[Self::Item]) -> Result<Self::Item, Self::Error> {
        if args.len() < 2 {
            return Err(Self::Error::from(FancyError::InvalidArgNum {
                got: args.len(),
                needed: 2,
            }));
        }
        args.iter()
            .skip(1)
            .fold(Ok(args[0].clone()), |acc, x| self.xor(&(acc?), x))
    }

    /// If `x = 0` returns the constant `b1` else return `b2`. Folds constants if possible.
    fn mux_constant_bits(
        &mut self,
        x: &Self::Item,
        b1: bool,
        b2: bool,
    ) -> Result<Self::Item, Self::Error> {
        match (b1, b2) {
            (false, true) => Ok(x.clone()),
            (true, false) => self.negate(x),
            (false, false) => self.constant(0, 2),
            (true, true) => self.constant(1, 2),
        }
    }

    /// If `b = 0` returns `x` else `y`.
    fn mux(
        &mut self,
        b: &Self::Item,
        x: &Self::Item,
        y: &Self::Item,
    ) -> Result<Self::Item, Self::Error> {
        let notb = self.negate(b)?;
        let xsel = self.and(&notb, x)?;
        let ysel = self.and(b, y)?;
        self.xor(&xsel, &ysel)
    }
}


pub trait Fancy {
    /// The underlying wire datatype created by an object implementing `Fancy`.
    type Item: Clone + HasModulus;

    /// Errors which may be thrown by the users of Fancy.
    type Error: std::fmt::Debug + std::fmt::Display + std::convert::From<FancyError>;

    /// Create a constant `x` with modulus `q`.
    fn constant(&mut self, x: u16, q: u16) -> Result<Self::Item, Self::Error>;

    /// Process this wire as output. Some `Fancy` implementers don't actually *return*
    /// output, but they need to be involved in the process, so they can return `None`.
    fn output(&mut self, x: &Self::Item) -> Result<Option<u16>, Self::Error>;

    /// Output a slice of wires.
    fn outputs(&mut self, xs: &[Self::Item]) -> Result<Option<Vec<u16>>, Self::Error> {
        let mut zs = Vec::with_capacity(xs.len());
        for x in xs.iter() {
            zs.push(self.output(x)?);
        }
        Ok(zs.into_iter().collect())
    }
}

pub trait FancyArithmetic: Fancy {
    /// Add `x` and `y`.
    fn add(&self, x: &Self::Item, y: &Self::Item) -> Result<Self::Item, Self::Error>;

    /// Subtract `x` and `y`.
    fn sub(&self, x: &Self::Item, y: &Self::Item) -> Result<Self::Item, Self::Error>;

    /// Multiply `x` times the constant `c`.
    fn cmul(&mut self, x: &Self::Item, c: u16) -> Result<Self::Item, Self::Error>;

    /// Multiply `x` and `y`.
    fn mul(&mut self, x: &Self::Item, y: &Self::Item) -> Result<Self::Item, Self::Error>;

    /// Project `x` according to the truth table `tt`. Resulting wire has modulus `q`.
    ///
    /// Optional `tt` is useful for hiding the gate from the evaluator.
    fn proj(
        &mut self,
        x: &Self::Item,
        q: u16,
        tt: Option<Vec<u16>>,
    ) -> Result<Self::Item, Self::Error>;

    ////////////////////////////////////////////////////////////////////////////////
    // Functions built on top of arithmetic fancy operations.

    /// Sum up a slice of wires.
    fn add_many(&mut self, args: &[Self::Item]) -> Result<Self::Item, Self::Error> {
        if args.len() < 2 {
            return Err(Self::Error::from(FancyError::InvalidArgNum {
                got: args.len(),
                needed: 2,
            }));
        }
        let mut z = args[0].clone();
        for x in args.iter().skip(1) {
            z = self.add(&z, x)?;
        }
        Ok(z)
    }
    /// Change the modulus of `x` to `to_modulus` using a projection gate.
    fn mod_change(&mut self, x: &Self::Item, to_modulus: u16) -> Result<Self::Item, Self::Error> {
        let from_modulus = x.modulus();
        if from_modulus == to_modulus {
            return Ok(x.clone());
        }
        let tab = (0..from_modulus).map(|x| x % to_modulus).collect_vec();
        self.proj(x, to_modulus, Some(tab))
    }
}

pub trait FancyReveal: Fancy {
    /// Reveal the contents of `x` to all parties.
    fn reveal(&mut self, x: &Self::Item) -> Result<u16, Self::Error>;

    /// Reveal a slice of items to all parties.
    fn reveal_many(&mut self, xs: &[Self::Item]) -> Result<Vec<u16>, Self::Error> {
        let mut zs = Vec::with_capacity(xs.len());
        for x in xs.iter() {
            zs.push(self.reveal(x)?);
        }
        Ok(zs)
    }

    /// Reveal a bundle to all parties.
    fn reveal_bundle(&mut self, x: &Bundle<Self::Item>) -> Result<Vec<u16>, Self::Error> {
        self.reveal_many(x.wires())
    }

    /// Reveal many bundles to all parties.
    fn reveal_many_bundles(
        &mut self,
        xs: &[Bundle<Self::Item>],
    ) -> Result<Vec<Vec<u16>>, Self::Error> {
        let mut zs = Vec::with_capacity(xs.len());
        for x in xs.iter() {
            zs.push(self.reveal_bundle(x)?);
        }
        Ok(zs)
    }



    /// Reveal a binary bundle to all parties.
    fn bin_reveal(&mut self, x: &BinaryBundle<Self::Item>) -> Result<u128, Self::Error> {
        let bits = self.reveal_many(x.wires())?;
        Ok(util::u128_from_bits(&bits))
    }

    /// Reveal many binary bundles to all parties.
    fn bin_reveal_many(
        &mut self,
        xs: &[BinaryBundle<Self::Item>],
    ) -> Result<Vec<u128>, Self::Error> {
        let mut zs = Vec::with_capacity(xs.len());
        for x in xs.iter() {
            zs.push(self.bin_reveal(x)?);
        }
        Ok(zs)
    }
}

/// Bundle which is explicitly binary representation.
#[derive(Clone)]
pub struct BinaryBundle<W>(Bundle<W>);

impl<W: Clone + HasModulus> BinaryBundle<W> {
    /// Create a new binary bundle from a vector of wires.
    pub fn new(ws: Vec<W>) -> BinaryBundle<W> {
        BinaryBundle(Bundle::new(ws))
    }

    /// Extract the underlying bundle from this binary bundle.
    pub fn extract(self) -> Bundle<W> {
        self.0
    }
}

impl<W: Clone + HasModulus> Deref for BinaryBundle<W> {
    type Target = Bundle<W>;

    fn deref(&self) -> &Bundle<W> {
        &self.0
    }
}

impl<W: Clone + HasModulus> DerefMut for BinaryBundle<W> {
    fn deref_mut(&mut self) -> &mut Bundle<W> {
        &mut self.0
    }
}

impl<W: Clone + HasModulus> From<Bundle<W>> for BinaryBundle<W> {
    fn from(b: Bundle<W>) -> BinaryBundle<W> {
        debug_assert!(b.moduli().iter().all(|&p| p == 2));
        BinaryBundle(b)
    }
}

impl<F: FancyBinary> BinaryGadgets for F {}

pub trait BinaryGadgets: FancyBinary + BundleGadgets {
    /// Create a constant bundle using base 2 inputs.
    fn bin_constant_bundle(
        &mut self,
        val: u128,
        nbits: usize,
    ) -> Result<BinaryBundle<Self::Item>, Self::Error> {
        self.constant_bundle(&util::u128_to_bits(val, nbits), &vec![2; nbits])
            .map(BinaryBundle)
    }

    /// Output a binary bundle and interpret the result as a `u128`.
    fn bin_output(&mut self, x: &BinaryBundle<Self::Item>) -> Result<Option<u128>, Self::Error> {
        Ok(self.output_bundle(x)?.map(|bs| util::u128_from_bits(&bs)))
    }

    /// Output a slice of binary bundles and interpret the results as a `u128`.
    fn bin_outputs(
        &mut self,
        xs: &[BinaryBundle<Self::Item>],
    ) -> Result<Option<Vec<u128>>, Self::Error> {
        let mut zs = Vec::with_capacity(xs.len());
        for x in xs.iter() {
            let z = self.bin_output(x)?;
            zs.push(z);
        }
        Ok(zs.into_iter().collect())
    }

    /// Xor the bits of two bundles together pairwise.
    fn bin_xor(
        &self,
        x: &BinaryBundle<Self::Item>,
        y: &BinaryBundle<Self::Item>,
    ) -> Result<BinaryBundle<Self::Item>, Self::Error> {
        x.wires()
            .iter()
            .zip(y.wires().iter())
            .map(|(x, y)| self.xor(x, y))
            .collect::<Result<Vec<Self::Item>, Self::Error>>()
            .map(BinaryBundle::new)
    }

    /// And the bits of two bundles together pairwise.
    fn bin_and(
        &mut self,
        x: &BinaryBundle<Self::Item>,
        y: &BinaryBundle<Self::Item>,
    ) -> Result<BinaryBundle<Self::Item>, Self::Error> {
        x.wires()
            .iter()
            .zip(y.wires().iter())
            .map(|(x, y)| self.and(x, y))
            .collect::<Result<Vec<Self::Item>, Self::Error>>()
            .map(BinaryBundle::new)
    }

    /// Or the bits of two bundles together pairwise.
    fn bin_or(
        &mut self,
        x: &BinaryBundle<Self::Item>,
        y: &BinaryBundle<Self::Item>,
    ) -> Result<BinaryBundle<Self::Item>, Self::Error> {
        x.wires()
            .iter()
            .zip(y.wires().iter())
            .map(|(x, y)| self.or(x, y))
            .collect::<Result<Vec<Self::Item>, Self::Error>>()
            .map(BinaryBundle::new)
    }

    /// Binary addition. Returns the result and the carry.
    fn bin_addition(
        &mut self,
        xs: &BinaryBundle<Self::Item>,
        ys: &BinaryBundle<Self::Item>,
    ) -> Result<(BinaryBundle<Self::Item>, Self::Item), Self::Error> {
        if xs.moduli() != ys.moduli() {
            return Err(Self::Error::from(FancyError::UnequalModuli));
        }
        let xwires = xs.wires();
        let ywires = ys.wires();
        let (mut z, mut c) = self.adder(&xwires[0], &ywires[0], None)?;
        let mut bs = vec![z];
        for i in 1..xwires.len() {
            let res = self.adder(&xwires[i], &ywires[i], Some(&c))?;
            z = res.0;
            c = res.1;
            bs.push(z);
        }
        Ok((BinaryBundle::new(bs), c))
    }

    /// Binary addition. Avoids creating extra gates for the final carry.
    fn bin_addition_no_carry(
        &mut self,
        xs: &BinaryBundle<Self::Item>,
        ys: &BinaryBundle<Self::Item>,
    ) -> Result<BinaryBundle<Self::Item>, Self::Error> {
        if xs.moduli() != ys.moduli() {
            return Err(Self::Error::from(FancyError::UnequalModuli));
        }
        let xwires = xs.wires();
        let ywires = ys.wires();
        let (mut z, mut c) = self.adder(&xwires[0], &ywires[0], None)?;
        let mut bs = vec![z];
        for i in 1..xwires.len() - 1 {
            let res = self.adder(&xwires[i], &ywires[i], Some(&c))?;
            z = res.0;
            c = res.1;
            bs.push(z);
        }
        // xor instead of add
        z = self.xor_many(&[
            xwires.last().unwrap().clone(),
            ywires.last().unwrap().clone(),
            c,
        ])?;
        bs.push(z);
        Ok(BinaryBundle::new(bs))
    }

    /// Binary multiplication.
    ///
    /// Returns the lower-order half of the output bits, ie a number with the same number
    /// of bits as the inputs.
    fn bin_multiplication_lower_half(
        &mut self,
        xs: &BinaryBundle<Self::Item>,
        ys: &BinaryBundle<Self::Item>,
    ) -> Result<BinaryBundle<Self::Item>, Self::Error> {
        if xs.moduli() != ys.moduli() {
            return Err(Self::Error::from(FancyError::UnequalModuli));
        }

        let xwires = xs.wires();
        let ywires = ys.wires();

        let mut sum = xwires
            .iter()
            .map(|x| self.and(x, &ywires[0]))
            .collect::<Result<Vec<Self::Item>, Self::Error>>()
            .map(BinaryBundle::new)?;

        for i in 1..xwires.len() {
            let mul = xwires
                .iter()
                .map(|x| self.and(x, &ywires[i]))
                .collect::<Result<Vec<Self::Item>, Self::Error>>()
                .map(BinaryBundle::new)?;
            let shifted = self.shift(&mul, i).map(BinaryBundle)?;
            sum = self.bin_addition_no_carry(&sum, &shifted)?;
        }

        Ok(sum)
    }

    /// Full multiplier
    fn bin_mul(
        &mut self,
        xs: &BinaryBundle<Self::Item>,
        ys: &BinaryBundle<Self::Item>,
    ) -> Result<BinaryBundle<Self::Item>, Self::Error> {
        if xs.moduli() != ys.moduli() {
            return Err(Self::Error::from(FancyError::UnequalModuli));
        }

        let xwires = xs.wires();
        let ywires = ys.wires();

        let mut sum = xwires
            .iter()
            .map(|x| self.and(x, &ywires[0]))
            .collect::<Result<_, _>>()
            .map(BinaryBundle::new)?;

        let zero = self.constant(0, 2)?;
        sum.pad(&zero, 1);

        for i in 1..xwires.len() {
            let mul = xwires
                .iter()
                .map(|x| self.and(x, &ywires[i]))
                .collect::<Result<_, _>>()
                .map(BinaryBundle::new)?;
            let shifted = self.shift_extend(&mul, i).map(BinaryBundle::from)?;
            let res = self.bin_addition(&sum, &shifted)?;
            sum = res.0;
            sum.push(res.1);
        }

        Ok(sum)
    }

    /// Divider
    fn bin_div(
        &mut self,
        xs: &BinaryBundle<Self::Item>,
        ys: &BinaryBundle<Self::Item>,
    ) -> Result<BinaryBundle<Self::Item>, Self::Error> {
        if xs.moduli() != ys.moduli() {
            return Err(Self::Error::from(FancyError::UnequalModuli));
        }
        let ys_neg = self.bin_twos_complement(ys)?;
        let mut acc = self.bin_constant_bundle(0, xs.size())?;
        let mut qs = BinaryBundle::new(Vec::new());
        for x in xs.iter().rev() {
            acc.pop();
            acc.insert(0, x.clone());
            let (res, cout) = self.bin_addition(&acc, &ys_neg)?;
            acc = self.bin_multiplex(&cout, &acc, &res)?;
            qs.push(cout);
        }
        qs.reverse(); // Switch back to little-endian
        Ok(qs)
    }

    /// Compute the twos complement of the input bundle (which must be base 2).
    fn bin_twos_complement(
        &mut self,
        xs: &BinaryBundle<Self::Item>,
    ) -> Result<BinaryBundle<Self::Item>, Self::Error> {
        let not_xs = xs
            .wires()
            .iter()
            .map(|x| self.negate(x))
            .collect::<Result<Vec<Self::Item>, Self::Error>>()
            .map(BinaryBundle::new)?;
        let one = self.bin_constant_bundle(1, xs.size())?;
        self.bin_addition_no_carry(&not_xs, &one)
    }

    /// Subtract two binary bundles. Returns the result and whether it underflowed.
    ///
    /// Due to the way that `twos_complement(0) = 0`, underflow indicates `y != 0 && x >= y`.
    fn bin_subtraction(
        &mut self,
        xs: &BinaryBundle<Self::Item>,
        ys: &BinaryBundle<Self::Item>,
    ) -> Result<(BinaryBundle<Self::Item>, Self::Item), Self::Error> {
        let neg_ys = self.bin_twos_complement(ys)?;
        self.bin_addition(xs, &neg_ys)
    }

    /// If `x=0` return `c1` as a bundle of constant bits, else return `c2`.
    fn bin_multiplex_constant_bits(
        &mut self,
        x: &Self::Item,
        c1: u128,
        c2: u128,
        nbits: usize,
    ) -> Result<BinaryBundle<Self::Item>, Self::Error> {
        let c1_bs = util::u128_to_bits(c1, nbits)
            .into_iter()
            .map(|x: u16| x > 0)
            .collect_vec();
        let c2_bs = util::u128_to_bits(c2, nbits)
            .into_iter()
            .map(|x: u16| x > 0)
            .collect_vec();
        c1_bs
            .into_iter()
            .zip(c2_bs.into_iter())
            .map(|(b1, b2)| self.mux_constant_bits(x, b1, b2))
            .collect::<Result<Vec<Self::Item>, Self::Error>>()
            .map(BinaryBundle::new)
    }

    /// Multiplex gadget for binary bundles
    fn bin_multiplex(
        &mut self,
        b: &Self::Item,
        x: &BinaryBundle<Self::Item>,
        y: &BinaryBundle<Self::Item>,
    ) -> Result<BinaryBundle<Self::Item>, Self::Error> {
        x.wires()
            .iter()
            .zip(y.wires().iter())
            .map(|(xwire, ywire)| self.mux(b, xwire, ywire))
            .collect::<Result<Vec<Self::Item>, Self::Error>>()
            .map(BinaryBundle::new)
    }

    /// Write the constant in binary and that gives you the shift amounts, Eg.. 7x is 4x+2x+x.
    fn bin_cmul(
        &mut self,
        x: &BinaryBundle<Self::Item>,
        c: u128,
        nbits: usize,
    ) -> Result<BinaryBundle<Self::Item>, Self::Error> {
        let zero = self.bin_constant_bundle(0, nbits)?;
        util::u128_to_bits(c, nbits)
            .into_iter()
            .enumerate()
            .filter_map(|(i, b)| if b > 0 { Some(i) } else { None })
            .fold(Ok(zero), |z, shift_amt| {
                let s = self.shift(x, shift_amt).map(BinaryBundle)?;
                self.bin_addition_no_carry(&(z?), &s)
            })
    }

    /// Compute the absolute value of a binary bundle.
    fn bin_abs(
        &mut self,
        x: &BinaryBundle<Self::Item>,
    ) -> Result<BinaryBundle<Self::Item>, Self::Error> {
        let sign = x.wires().last().unwrap();
        let negated = self.bin_twos_complement(x)?;
        self.bin_multiplex(sign, x, &negated)
    }

    /// Returns 1 if `x < y` (signed version)
    fn bin_lt_signed(
        &mut self,
        x: &BinaryBundle<Self::Item>,
        y: &BinaryBundle<Self::Item>,
    ) -> Result<Self::Item, Self::Error> {
        // determine whether x and y are positive or negative
        let x_neg = &x.wires().last().unwrap();
        let y_neg = &y.wires().last().unwrap();
        let x_pos = self.negate(x_neg)?;
        let y_pos = self.negate(y_neg)?;

        // broken into cases based on x and y being negative or positive
        // base case: if x and y have the same sign - use unsigned lt
        let x_lt_y_unsigned = self.bin_lt(x, y)?;

        // if x is negative and y is positive then x < y
        let tru = self.constant(1, 2)?;
        let x_neg_y_pos = self.and(x_neg, &y_pos)?;
        let r2 = self.mux(&x_neg_y_pos, &x_lt_y_unsigned, &tru)?;

        // if x is positive and y is negative then !(x < y)
        let fls = self.constant(0, 2)?;
        let x_pos_y_neg = self.and(&x_pos, y_neg)?;
        self.mux(&x_pos_y_neg, &r2, &fls)
    }

    /// Returns 1 if `x < y`.
    fn bin_lt(
        &mut self,
        x: &BinaryBundle<Self::Item>,
        y: &BinaryBundle<Self::Item>,
    ) -> Result<Self::Item, Self::Error> {
        // underflow indicates y != 0 && x >= y
        // requiring special care to remove the y != 0, which is what follows.
        let (_, lhs) = self.bin_subtraction(x, y)?;

        // Now we build a clause equal to (y == 0 || x >= y), which we can OR with
        // lhs to remove the y==0 aspect.
        // check if y==0
        let y_contains_1 = self.or_many(y.wires())?;
        let y_eq_0 = self.negate(&y_contains_1)?;

        // if x != 0, then x >= y, ... assuming x is not negative
        let x_contains_1 = self.or_many(x.wires())?;

        // y == 0 && x >= y
        let rhs = self.and(&y_eq_0, &x_contains_1)?;

        // (y != 0 && x >= y) || (y == 0 && x >= y)
        // => x >= y && (y != 0 || y == 0)\
        // => x >= y && 1
        // => x >= y
        let geq = self.or(&lhs, &rhs)?;
        let ngeq = self.negate(&geq)?;

        let xy_neq_0 = self.or(&y_contains_1, &x_contains_1)?;
        self.and(&xy_neq_0, &ngeq)
    }

    /// Returns 1 if `x >= y`.
    fn bin_geq(
        &mut self,
        x: &BinaryBundle<Self::Item>,
        y: &BinaryBundle<Self::Item>,
    ) -> Result<Self::Item, Self::Error> {
        let z = self.bin_lt(x, y)?;
        self.negate(&z)
    }

    /// Compute the maximum bundle in `xs`.
    fn bin_max(
        &mut self,
        xs: &[BinaryBundle<Self::Item>],
    ) -> Result<BinaryBundle<Self::Item>, Self::Error> {
        if xs.is_empty() {
            return Err(Self::Error::from(FancyError::InvalidArgNum {
                got: xs.len(),
                needed: 1,
            }));
        }
        xs.iter().skip(1).fold(Ok(xs[0].clone()), |x, y| {
            x.map(|x| {
                let pos = self.bin_lt(&x, y)?;
                let neg = self.negate(&pos)?;
                x.wires()
                    .iter()
                    .zip(y.wires().iter())
                    .map(|(x, y)| {
                        let xp = self.and(x, &neg)?;
                        let yp = self.and(y, &pos)?;
                        self.xor(&xp, &yp)
                    })
                    .collect::<Result<Vec<Self::Item>, Self::Error>>()
                    .map(BinaryBundle::new)
            })?
        })
    }

    /// Demux a binary bundle into a unary vector.
    fn bin_demux(&mut self, x: &BinaryBundle<Self::Item>) -> Result<Vec<Self::Item>, Self::Error> {
        let wires = x.wires();
        let nbits = wires.len();
        if nbits > 8 {
            return Err(Self::Error::from(FancyError::InvalidArg(
                "wire bitlength too large".to_string(),
            )));
        }

        let mut outs = Vec::with_capacity(1 << nbits);

        for ix in 0..1 << nbits {
            let mut acc = wires[0].clone();
            if (ix & 1) == 0 {
                acc = self.negate(&acc)?;
            }
            for (i, w) in wires.iter().enumerate().skip(1) {
                if ((ix >> i) & 1) > 0 {
                    acc = self.and(&acc, w)?;
                } else {
                    let not_w = self.negate(w)?;
                    acc = self.and(&acc, &not_w)?;
                }
            }
            outs.push(acc);
        }

        Ok(outs)
    }

    /// arithmetic right shift (shifts the sign of the MSB into the new spaces)
    fn bin_rsa(
        &mut self,
        x: &BinaryBundle<Self::Item>,
        c: usize,
    ) -> Result<BinaryBundle<Self::Item>, Self::Error> {
        self.bin_shr(x, c, x.wires().last().unwrap())
    }

    /// logical right shift (shifts 0 into the empty spaces)
    fn bin_rsl(
        &mut self,
        x: &BinaryBundle<Self::Item>,
        c: usize,
    ) -> Result<BinaryBundle<Self::Item>, Self::Error> {
        let zero = self.constant(0, 2)?;
        self.bin_shr(x, c, &zero)
    }

    /// shift a value right by a constant, filling space on the right by `pad`
    fn bin_shr(
        &mut self,
        x: &BinaryBundle<Self::Item>,
        c: usize,
        pad: &Self::Item,
    ) -> Result<BinaryBundle<Self::Item>, Self::Error> {
        let mut wires: Vec<Self::Item> = Vec::with_capacity(x.wires().len());

        for i in 0..x.wires().len() {
            let src_idx = i + c;
            if src_idx >= x.wires().len() {
                wires.push(pad.clone())
            } else {
                wires.push(x.wires()[src_idx].clone())
            }
        }

        Ok(BinaryBundle::new(wires))
    }
    /// Compute `x == y` for binary bundles.
    fn bin_eq_bundles(
        &mut self,
        x: &BinaryBundle<Self::Item>,
        y: &BinaryBundle<Self::Item>,
    ) -> Result<Self::Item, Self::Error> {
        // compute (x^y == 0) for each residue
        let zs = x
            .wires()
            .iter()
            .zip_eq(y.wires().iter())
            .map(|(x, y)| {
                let xy = self.xor(x, y)?;
                self.negate(&xy)
            })
            .collect::<Result<Vec<Self::Item>, Self::Error>>()?;
        // and_many will return 1 only if all outputs of xnor are 1
        // indicating equality
        self.and_many(&zs)
    }
}


/// A collection of wires, useful for the garbled gadgets defined by `BundleGadgets`.
#[derive(Clone)]
pub struct Bundle<W>(Vec<W>);

impl<W: Clone + HasModulus> Bundle<W> {
    /// Create a new bundle from some wires.
    pub fn new(ws: Vec<W>) -> Bundle<W> {
        Bundle(ws)
    }

    /// Return the moduli of all the wires in the bundle.
    pub fn moduli(&self) -> Vec<u16> {
        self.0.iter().map(HasModulus::modulus).collect()
    }

    /// Extract the wires from this bundle.
    pub fn wires(&self) -> &[W] {
        &self.0
    }

    /// Get the number of wires in this bundle.
    pub fn size(&self) -> usize {
        self.0.len()
    }

    /// Whether this bundle only contains residues in mod 2.
    pub fn is_binary(&self) -> bool {
        self.moduli().iter().all(|m| *m == 2)
    }

    /// Returns a new bundle only containing wires with matching moduli.
    pub fn with_moduli(&self, moduli: &[u16]) -> Bundle<W> {
        let old_ws = self.wires();
        let mut new_ws = Vec::with_capacity(moduli.len());
        for &p in moduli {
            if let Some(w) = old_ws.iter().find(|&x| x.modulus() == p) {
                new_ws.push(w.clone());
            } else {
                panic!("Bundle::with_moduli: no {} modulus in bundle", p);
            }
        }
        Bundle(new_ws)
    }

    /// Pad the Bundle with val, n times.
    pub fn pad(&mut self, val: &W, n: usize) {
        for _ in 0..n {
            self.0.push(val.clone());
        }
    }

    /// Extract a wire from the Bundle, removing it and returning it.
    pub fn extract(&mut self, wire_index: usize) -> W {
        self.0.remove(wire_index)
    }

    /// Insert a wire from the Bundle
    pub fn insert(&mut self, wire_index: usize, val: W) {
        self.0.insert(wire_index, val)
    }

    /// push a wire onto the Bundle.
    pub fn push(&mut self, val: W) {
        self.0.push(val);
    }

    /// Pop a wire from the Bundle.
    pub fn pop(&mut self) -> Option<W> {
        self.0.pop()
    }

    /// Access the underlying iterator
    pub fn iter(&self) -> std::slice::Iter<W> {
        self.0.iter()
    }

    /// Reverse the wires
    pub fn reverse(&mut self) {
        self.0.reverse();
    }
}

impl<W: Clone + HasModulus> Index<usize> for Bundle<W> {
    type Output = W;

    fn index(&self, idx: usize) -> &Self::Output {
        self.0.index(idx)
    }
}

impl<F: Fancy> BundleGadgets for F {}
impl<F: FancyArithmetic> ArithmeticBundleGadgets for F {}
impl<F: FancyBinary> BinaryBundleGadgets for F {}

/// Arithmetic operations on wire bundles, extending the capability of `FancyArithmetic` operating
/// on individual wires.
pub trait ArithmeticBundleGadgets: FancyArithmetic {
    /// Add two wire bundles pairwise, zipping addition.
    ///
    /// In CRT this is plain addition. In binary this is xor.
    fn add_bundles(
        &mut self,
        x: &Bundle<Self::Item>,
        y: &Bundle<Self::Item>,
    ) -> Result<Bundle<Self::Item>, Self::Error> {
        if x.wires().len() != y.wires().len() {
            return Err(Self::Error::from(FancyError::InvalidArgNum {
                got: y.wires().len(),
                needed: x.wires().len(),
            }));
        }
        x.wires()
            .iter()
            .zip(y.wires().iter())
            .map(|(x, y)| self.add(x, y))
            .collect::<Result<Vec<Self::Item>, Self::Error>>()
            .map(Bundle::new)
    }

    /// Subtract two wire bundles, residue by residue.
    ///
    /// In CRT this is plain subtraction. In binary this is `xor`.
    fn sub_bundles(
        &mut self,
        x: &Bundle<Self::Item>,
        y: &Bundle<Self::Item>,
    ) -> Result<Bundle<Self::Item>, Self::Error> {
        if x.wires().len() != y.wires().len() {
            return Err(Self::Error::from(FancyError::InvalidArgNum {
                got: y.wires().len(),
                needed: x.wires().len(),
            }));
        }
        x.wires()
            .iter()
            .zip(y.wires().iter())
            .map(|(x, y)| self.sub(x, y))
            .collect::<Result<Vec<Self::Item>, Self::Error>>()
            .map(Bundle::new)
    }

    /// Multiply each wire in `x` with each wire in `y`, pairwise.
    ///
    /// In CRT this is plain multiplication. In binary this is `and`.
    fn mul_bundles(
        &mut self,
        x: &Bundle<Self::Item>,
        y: &Bundle<Self::Item>,
    ) -> Result<Bundle<Self::Item>, Self::Error> {
        x.wires()
            .iter()
            .zip(y.wires().iter())
            .map(|(x, y)| self.mul(x, y))
            .collect::<Result<Vec<Self::Item>, Self::Error>>()
            .map(Bundle::new)
    }

    /// Mixed radix addition.
    fn mixed_radix_addition(
        &mut self,
        xs: &[Bundle<Self::Item>],
    ) -> Result<Bundle<Self::Item>, Self::Error> {
        let nargs = xs.len();
        if nargs < 1 {
            return Err(Self::Error::from(FancyError::InvalidArgNum {
                got: nargs,
                needed: 1,
            }));
        }

        let n = xs[0].wires().len();
        if !xs.iter().all(|x| x.moduli() == xs[0].moduli()) {
            return Err(Self::Error::from(FancyError::UnequalModuli));
        }

        let mut digit_carry = None;
        let mut carry_carry = None;
        let mut max_carry = 0;

        let mut res = Vec::with_capacity(n);

        for i in 0..n {
            // all the ith digits, in one vec
            let ds = xs.iter().map(|x| x.wires()[i].clone()).collect_vec();

            // compute the digit -- easy
            let digit_sum = self.add_many(&ds)?;
            let digit = digit_carry.map_or(Ok(digit_sum.clone()), |d| self.add(&digit_sum, &d))?;

            if i < n - 1 {
                // compute the carries
                let q = xs[0].wires()[i].modulus();
                // max_carry currently contains the max carry from the previous iteration
                let max_val = nargs as u16 * (q - 1) + max_carry;
                // now it is the max carry of this iteration
                max_carry = max_val / q;

                let modded_ds = ds
                    .iter()
                    .map(|d| self.mod_change(d, max_val + 1))
                    .collect::<Result<Vec<Self::Item>, Self::Error>>()?;

                let carry_sum = self.add_many(&modded_ds)?;
                // add in the carry from the previous iteration
                let carry =
                    carry_carry.map_or(Ok(carry_sum.clone()), |c| self.add(&carry_sum, &c))?;

                // carry now contains the carry information, we just have to project it to
                // the correct moduli for the next iteration
                let next_mod = xs[0].wires()[i + 1].modulus();
                let tt = (0..=max_val).map(|i| (i / q) % next_mod).collect_vec();
                digit_carry = Some(self.proj(&carry, next_mod, Some(tt))?);

                let next_max_val = nargs as u16 * (next_mod - 1) + max_carry;

                if i < n - 2 {
                    if max_carry < next_mod {
                        carry_carry =
                            Some(self.mod_change(digit_carry.as_ref().unwrap(), next_max_val + 1)?);
                    } else {
                        let tt = (0..=max_val).map(|i| i / q).collect_vec();
                        carry_carry = Some(self.proj(&carry, next_max_val + 1, Some(tt))?);
                    }
                } else {
                    // next digit is MSB so we dont need carry_carry
                    carry_carry = None;
                }
            } else {
                digit_carry = None;
                carry_carry = None;
            }
            res.push(digit);
        }
        Ok(Bundle(res))
    }

    /// Mixed radix addition only returning the MSB.
    fn mixed_radix_addition_msb_only(
        &mut self,
        xs: &[Bundle<Self::Item>],
    ) -> Result<Self::Item, Self::Error> {
        let nargs = xs.len();
        if nargs < 1 {
            return Err(Self::Error::from(FancyError::InvalidArgNum {
                got: nargs,
                needed: 1,
            }));
        }

        let n = xs[0].wires().len();
        if !xs.iter().all(|x| x.moduli() == xs[0].moduli()) {
            return Err(Self::Error::from(FancyError::UnequalModuli));
        }

        let mut opt_carry = None;
        let mut max_carry = 0;

        for i in 0..n - 1 {
            // all the ith digits, in one vec
            let ds = xs.iter().map(|x| x.wires()[i].clone()).collect_vec();
            // compute the carry
            let q = xs[0].moduli()[i];
            // max_carry currently contains the max carry from the previous iteration
            let max_val = nargs as u16 * (q - 1) + max_carry;
            // now it is the max carry of this iteration
            max_carry = max_val / q;

            // mod change the digits to the max sum possible plus the max carry of the
            // previous iteration
            let modded_ds = ds
                .iter()
                .map(|d| self.mod_change(d, max_val + 1))
                .collect::<Result<Vec<Self::Item>, Self::Error>>()?;
            // add them up
            let sum = self.add_many(&modded_ds)?;
            // add in the carry
            let sum_with_carry = opt_carry
                .as_ref()
                .map_or(Ok(sum.clone()), |c| self.add(&sum, c))?;

            // carry now contains the carry information, we just have to project it to
            // the correct moduli for the next iteration. It will either be used to
            // compute the next carry, if i < n-2, or it will be used to compute the
            // output MSB, in which case it should be the modulus of the SB
            let next_mod = if i < n - 2 {
                nargs as u16 * (xs[0].moduli()[i + 1] - 1) + max_carry + 1
            } else {
                xs[0].moduli()[i + 1] // we will be adding the carry to the MSB
            };

            let tt = (0..=max_val).map(|i| (i / q) % next_mod).collect_vec();
            opt_carry = Some(self.proj(&sum_with_carry, next_mod, Some(tt))?);
        }

        // compute the msb
        let ds = xs.iter().map(|x| x.wires()[n - 1].clone()).collect_vec();
        let digit_sum = self.add_many(&ds)?;
        opt_carry
            .as_ref()
            .map_or(Ok(digit_sum.clone()), |d| self.add(&digit_sum, d))
    }

    /// If b=0 then return 0, else return x.
    fn mask(
        &mut self,
        b: &Self::Item,
        x: &Bundle<Self::Item>,
    ) -> Result<Bundle<Self::Item>, Self::Error> {
        x.wires()
            .iter()
            .map(|xwire| self.mul(xwire, b))
            .collect::<Result<Vec<Self::Item>, Self::Error>>()
            .map(Bundle)
    }

    /// Compute `x == y`. Returns a wire encoding the result mod 2.
    fn eq_bundles(
        &mut self,
        x: &Bundle<Self::Item>,
        y: &Bundle<Self::Item>,
    ) -> Result<Self::Item, Self::Error> {
        if x.moduli() != y.moduli() {
            return Err(Self::Error::from(FancyError::UnequalModuli));
        }
        let wlen = x.wires().len() as u16;
        let zs = x
            .wires()
            .iter()
            .zip_eq(y.wires().iter())
            .map(|(x, y)| {
                // compute (x-y == 0) for each residue
                let z = self.sub(x, y)?;
                let mut eq_zero_tab = vec![0; x.modulus() as usize];
                eq_zero_tab[0] = 1;
                self.proj(&z, wlen + 1, Some(eq_zero_tab))
            })
            .collect::<Result<Vec<Self::Item>, Self::Error>>()?;
        // add up the results, and output whether they equal zero or not, mod 2
        let z = self.add_many(&zs)?;
        let b = zs.len();
        let mut tab = vec![0; b + 1];
        tab[b] = 1;
        self.proj(&z, 2, Some(tab))
    }
}

/// Binary operations on wire bundles, extending the capability of `FancyBinary` operating
/// on individual wires.
pub trait BinaryBundleGadgets: FancyBinary {
    /// If b=0 then return x, else return y.
    fn multiplex(
        &mut self,
        b: &Self::Item,
        x: &Bundle<Self::Item>,
        y: &Bundle<Self::Item>,
    ) -> Result<Bundle<Self::Item>, Self::Error> {
        x.wires()
            .iter()
            .zip(y.wires().iter())
            .map(|(xwire, ywire)| self.mux(b, xwire, ywire))
            .collect::<Result<Vec<Self::Item>, Self::Error>>()
            .map(Bundle)
    }
}

pub trait BundleGadgets: Fancy {
    /// Creates a bundle of constant wires using moduli `ps`.
    fn constant_bundle(
        &mut self,
        xs: &[u16],
        ps: &[u16],
    ) -> Result<Bundle<Self::Item>, Self::Error> {
        xs.iter()
            .zip(ps.iter())
            .map(|(&x, &p)| self.constant(x, p))
            .collect::<Result<Vec<Self::Item>, Self::Error>>()
            .map(Bundle)
    }

    /// Output the wires that make up a bundle.
    fn output_bundle(&mut self, x: &Bundle<Self::Item>) -> Result<Option<Vec<u16>>, Self::Error> {
        let ws = x.wires();
        let mut outputs = Vec::with_capacity(ws.len());
        for w in ws.iter() {
            outputs.push(self.output(w)?);
        }
        Ok(outputs.into_iter().collect())
    }

    /// Output a slice of bundles.
    fn output_bundles(
        &mut self,
        xs: &[Bundle<Self::Item>],
    ) -> Result<Option<Vec<Vec<u16>>>, Self::Error> {
        let mut zs = Vec::with_capacity(xs.len());
        for x in xs.iter() {
            let z = self.output_bundle(x)?;
            zs.push(z);
        }
        Ok(zs.into_iter().collect())
    }

    ////////////////////////////////////////////////////////////////////////////////
    // gadgets which are neither CRT or binary

    /// Shift residues, replacing them with zeros in the modulus of the least signifigant
    /// residue. Maintains the length of the input.
    fn shift(
        &mut self,
        x: &Bundle<Self::Item>,
        n: usize,
    ) -> Result<Bundle<Self::Item>, Self::Error> {
        let mut ws = x.wires().to_vec();
        let zero = self.constant(0, ws.last().unwrap().modulus())?;
        for _ in 0..n {
            ws.pop();
            ws.insert(0, zero.clone());
        }
        Ok(Bundle(ws))
    }

    /// Shift residues, replacing them with zeros in the modulus of the least signifigant
    /// residue. Output is extended with n elements.
    fn shift_extend(
        &mut self,
        x: &Bundle<Self::Item>,
        n: usize,
    ) -> Result<Bundle<Self::Item>, Self::Error> {
        let mut ws = x.wires().to_vec();
        let zero = self.constant(0, ws.last().unwrap().modulus())?;
        for _ in 0..n {
            ws.insert(0, zero.clone());
        }
        Ok(Bundle(ws))
    }
}
