use nom::{
    branch,
    bytes::{self, complete},
    character, combinator, sequence,
};
use std::fmt::Write;

use super::helpers;

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum AssignmentKind {
    /// Assignment to a bitvector.
    BitVec {
        /// Value of the bitvector at the given transition.
        value: u64,
        /// Number of bits in the bitvector.
        bits: usize,
    },

    /// Assignment to an array of bitvectors.
    Array {
        /// Index in the array
        index: u64,
        /// Value of the bitvector at `index` at the given transition.
        value: u64,
        /// Number of bits the bitvector
        bits: usize,
    },
}

impl AssignmentKind {
    pub fn to_binary_string(self) -> String {
        let (bits, extra) = match self {
            AssignmentKind::BitVec { bits, .. } => (bits, 0),
            AssignmentKind::Array { bits, .. } => (bits * 2, 4),
        };

        let mut buf = String::with_capacity(bits + extra);

        let write_bits = |buf: &mut String, value, len: usize| {
            (0..len).rev().for_each(|i| {
                let bit = (value >> i) & 1;
                write!(buf, "{}", bit).expect("Writing to string is infallible.");
            });
        };

        match self {
            AssignmentKind::BitVec { value, .. } => write_bits(&mut buf, value, bits),
            AssignmentKind::Array { value, index, .. } => {
                buf.push('[');
                write_bits(&mut buf, index, bits / 2);
                buf.push(']');

                buf.push_str(" -> ");

                write_bits(&mut buf, value, bits / 2);
            }
        };

        buf
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Assignment {
    pub kind: AssignmentKind,
    pub symbol: Option<String>,
}

impl Assignment {
    pub fn parse(input: &str) -> nom::IResult<&str, Assignment> {
        let (input, _uint) = helpers::uint(input)?;

        let (input, _whitespace) = character::complete::space0(input)?;

        let (input, assignment) = branch::alt((bitvec_assign, array_assign))(input)?;

        let (input, _whitespace) = character::complete::space0(input)?;

        let (input, symbol) = combinator::opt(symbol)(input)?;

        let (input, _newline) = helpers::newline(input)?;

        Ok((
            input,
            Assignment {
                kind: assignment,
                symbol: symbol.map(String::from),
            },
        ))
    }

    pub fn get_value(&self) -> u64 {
        match self.kind {
            AssignmentKind::BitVec { value, .. } => value,
            AssignmentKind::Array { value, .. } => value,
        }
    }
}

impl std::fmt::Debug for Assignment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(symbol) = &self.symbol {
            write!(f, "{} = ", symbol)?;
        }

        write!(f, "{}", self.kind.to_binary_string())?;

        Ok(())
    }
}

fn symbol(input: &str) -> nom::IResult<&str, &str> {
    let (input, mut symbol) =
        complete::take_while1(|txt: char| txt.is_ascii() && txt != '\n')(input)?;

    if let Some(idx) = symbol.find('@') {
        symbol = &symbol[..idx];
    }

    Ok((input, symbol))
}

fn binary_string(input: &str) -> nom::IResult<&str, &str> {
    bytes::complete::take_while1(|i| i == '0' || i == '1')(input)
}

fn bitvec_assign(input: &str) -> nom::IResult<&str, AssignmentKind> {
    combinator::map(binary_string, |val| {
        let value = u64::from_str_radix(val, 2).expect("binary_string parses only 0s and 1s.");

        AssignmentKind::BitVec {
            value,
            bits: val.len(),
        }
    })(input)
}

fn array_assign(input: &str) -> nom::IResult<&str, AssignmentKind> {
    let array_index = sequence::preceded(
        complete::tag("["),
        sequence::terminated(binary_string, complete::tag("]")),
    );

    let array_index = sequence::terminated(array_index, character::complete::space0);

    combinator::map(
        sequence::tuple((array_index, binary_string)),
        |(idx, value)| AssignmentKind::Array {
            index: idx.parse().expect("binary_string parses only 0s and 1s."),
            value: u64::from_str_radix(value, 2).expect("binary_string parses only 0s and 1s."),
            bits: value.len(),
        },
    )(input)
}
