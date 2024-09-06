use std::{
    collections::HashMap,
    io::{BufRead, BufReader, Read},
};

use serde::{Deserialize, Serialize};

use crate::btor::witness_format::PropKind;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Property {
    pub node: usize,
    pub _kind: PropKind,
    pub name: Option<String>,
}

pub(super) fn get_property_names<R: Read>(input: R) -> HashMap<u64, Property> {
    let input = BufReader::new(input);
    input
        .lines()
        .filter(|line| match line {
            Ok(line) => line
                .split(' ')
                .nth(1)
                .is_some_and(|kind| kind == "bad" || kind == "justice"),
            Err(_) => false,
        })
        .enumerate()
        .filter_map(|(idx, line)| {
            let line = line.ok()?;
            let mut iter = line.split(' ');
            let node = iter.next()?.parse().ok()?;
            let kind: PropKind = iter.next()?.parse().ok()?;
            let name = iter.nth(1).map(String::from);
            let idx = idx.try_into().ok()?;

            Some((
                idx,
                Property {
                    node,
                    _kind: kind,
                    name,
                },
            ))
        })
        .collect()
}
