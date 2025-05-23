use fancy_garbling::{
    errors::TwopacError, WireLabel, AllWire, ArithmeticWire, 
    // Fancy, FancyArithmetic, FancyBinary, FancyReveal, 
    WireMod2,
};
use ocelot::ot::Receiver as OtReceiver;
use rand::{CryptoRng, Rng};
use rayon::iter::{IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, ParallelIterator};
use scuttlebutt::{AbstractChannel, Block, SemiHonest};
use super::{inner_ev::Evaluator as Ev, traits::*};

/// Semi-honest evaluator.
pub struct Evaluator<C, RNG, OT, Wire> {
    evaluator: Ev<C, Wire>,
    ot: OT,
    rng: RNG,
}

impl<C, RNG, OT, Wire> Evaluator<C, RNG, OT, Wire> {}

impl<
        C: AbstractChannel,
        RNG: CryptoRng + Rng,
        OT: OtReceiver<Msg = Block> + SemiHonest,
        Wire: WireLabel,
    > Evaluator<C, RNG, OT, Wire>
{
    /// Make a new `Evaluator`.
    pub fn new(mut channel: C, mut rng: RNG) -> Result<Self, TwopacError> {
        let ot = OT::init(&mut channel, &mut rng)?;
        let evaluator = Ev::new(channel);
        Ok(Self { evaluator, ot, rng })
    }

    /// Get a reference to the internal channel.
    pub fn get_channel(&mut self) -> &mut C {
        &mut self.evaluator.channel
    }

    fn run_ot(&mut self, inputs: &[bool]) -> Result<Vec<Block>, TwopacError> {
        self.ot
            .receive(&mut self.evaluator.channel, inputs, &mut self.rng)
            .map_err(TwopacError::from)
    }
}

impl<
        C: AbstractChannel,
        RNG: CryptoRng + Rng,
        OT: OtReceiver<Msg = Block> + SemiHonest,
        Wire: WireLabel + Send + Sync,
    > FancyInput for Evaluator<C, RNG, OT, Wire>
{
    type Item = Wire;
    type Error = TwopacError;

    /// Receive a garbler input wire.
    fn receive(&mut self, modulus: u16) -> Result<Wire, TwopacError> {
        let w = self.evaluator.read_wire(modulus)?;
        Ok(w)
    }

    /// Receive garbler input wires.
    fn receive_many(&mut self, moduli: &[u16]) -> Result<Vec<Wire>, TwopacError> {
        moduli.iter().map(|q| self.receive(*q)).collect()
    }

    /// Perform OT and obtain wires for the evaluator's inputs.
    fn encode_many(&mut self, inputs: &[u16], moduli: &[u16]) -> Result<Vec<Wire>, TwopacError> {
        
        let (lens, bs): (Vec<_>, Vec<_>) = inputs
        .par_iter()
        .zip(moduli.par_iter())
        .map(|(&x, &q)| {
            let len = f32::from(q).log(2.0).ceil() as usize;
            let bs = (0..len).map(|i| x & (1 << i) != 0).collect::<Vec<_>>();
            (len, bs)
        })
        .unzip();

        // Flatten the `bs` vector of vectors into a single vector
        let bs: Vec<bool> = bs.into_par_iter().flatten().collect();

        let wires = self.run_ot(&bs)?;

        let mut c_starts = vec![0];
        for len in &lens {
            let last_start = *c_starts.last().unwrap();
            c_starts.push(last_start+len);
        }
        c_starts.pop();
        let res: Vec<Wire> = lens.into_par_iter().zip(moduli.par_iter()).zip(c_starts.into_par_iter()).map(|((len, q), start)| {
            let range = start..start+len;
            let chunk = &wires[range];
            combine(chunk, *q)
        }).collect();


        // let mut start = 0;
        // let res = lens
        // .into_iter()
        // .zip(moduli.iter())
        // .map(|(len, q)| {
        //     let range = start..start + len;
        //     let chunk = &wires[range];
        //     start += len;
        //     combine(chunk, *q)
        // })
        // .collect::<Vec<Wire>>();

        Ok(res)
    }
}

fn combine<Wire: WireLabel + Send>(wires: &[Block], q: u16) -> Wire {
    wires.iter().enumerate().fold(Wire::zero(q), |acc, (i, w)| {
        let w = Wire::from_block(*w, q);
        acc.plus(&w.cmul(1 << i))
    })
}

impl<C: AbstractChannel, RNG, OT> FancyBinary for Evaluator<C, RNG, OT, WireMod2> {
    fn and(&mut self, x: &Self::Item, y: &Self::Item) -> Result<Self::Item, Self::Error> {
        self.evaluator.and(x, y).map_err(Self::Error::from)
    }

    fn xor(&self, x: &Self::Item, y: &Self::Item) -> Result<Self::Item, Self::Error> {
        self.evaluator.xor(x, y).map_err(Self::Error::from)
    }

    fn negate(&self, x: &Self::Item) -> Result<Self::Item, Self::Error> {
        self.evaluator.negate(x).map_err(Self::Error::from)
    }
}

impl<C: AbstractChannel, RNG, OT> FancyBinary for Evaluator<C, RNG, OT, AllWire> {
    fn and(&mut self, x: &Self::Item, y: &Self::Item) -> Result<Self::Item, Self::Error> {
        self.evaluator.and(x, y).map_err(Self::Error::from)
    }

    fn xor(&self, x: &Self::Item, y: &Self::Item) -> Result<Self::Item, Self::Error> {
        self.evaluator.xor(x, y).map_err(Self::Error::from)
    }

    fn negate(&self, x: &Self::Item) -> Result<Self::Item, Self::Error> {
        self.evaluator.negate(x).map_err(Self::Error::from)
    }
}

impl<C: AbstractChannel, RNG, OT, Wire: WireLabel + ArithmeticWire> FancyArithmetic
    for Evaluator<C, RNG, OT, Wire>
{
    fn add(&self, x: &Wire, y: &Wire) -> Result<Self::Item, Self::Error> {
        self.evaluator.add(x, y).map_err(Self::Error::from)
    }

    fn sub(&self, x: &Wire, y: &Wire) -> Result<Self::Item, Self::Error> {
        self.evaluator.sub(x, y).map_err(Self::Error::from)
    }

    fn cmul(&mut self, x: &Wire, c: u16) -> Result<Self::Item, Self::Error> {
        self.evaluator.cmul(x, c).map_err(Self::Error::from)
    }

    fn mul(&mut self, x: &Wire, y: &Wire) -> Result<Self::Item, Self::Error> {
        self.evaluator.mul(x, y).map_err(Self::Error::from)
    }

    fn proj(&mut self, x: &Wire, q: u16, tt: Option<Vec<u16>>) -> Result<Self::Item, Self::Error> {
        self.evaluator.proj(x, q, tt).map_err(Self::Error::from)
    }
}

impl<C: AbstractChannel, RNG, OT, Wire: WireLabel> Fancy for Evaluator<C, RNG, OT, Wire> {
    type Item = Wire;
    type Error = TwopacError;

    fn constant(&mut self, x: u16, q: u16) -> Result<Self::Item, Self::Error> {
        self.evaluator.constant(x, q).map_err(Self::Error::from)
    }

    fn output(&mut self, x: &Wire) -> Result<Option<u16>, Self::Error> {
        self.evaluator.output(x).map_err(Self::Error::from)
    }
}

impl<C: AbstractChannel, RNG: CryptoRng + Rng, OT, Wire: WireLabel> FancyReveal
    for Evaluator<C, RNG, OT, Wire>
{
    fn reveal(&mut self, x: &Self::Item) -> Result<u16, Self::Error> {
        self.evaluator.reveal(x).map_err(Self::Error::from)
    }
}

impl<C: AbstractChannel, RNG, OT, Wire> SemiHonest for Evaluator<C, RNG, OT, Wire> {}
