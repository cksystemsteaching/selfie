mod assignment;
mod btor2;
mod helpers;
mod witness_format;

use std::{
    collections::{BTreeMap, HashMap},
    fmt::Write,
    io::Read,
    str::FromStr,
};

use nom::{branch, combinator, multi};

use self::{
    assignment::Assignment,
    btor2::Property,
    witness_format::{WitnessFormat, WitnessFrame},
};

pub use witness_format::{Prop, PropKind, PropVec};

pub fn parse_btor_witness<I: Read>(
    mut input: I,
    btor2: Option<impl Read>,
) -> anyhow::Result<Witness> {
    let mut buf = String::new();
    let _ = input.read_to_string(&mut buf);

    let mut witness = Witness::from_str(&buf)
        .map_err(|err| anyhow::format_err!("Failed to parse witness. Cause: {err}"))?;

    if let Some(btor2_prop_names) = btor2.map(|inner| btor2::get_property_names(inner)) {
        witness.add_prop_names(btor2_prop_names);
    }

    Ok(witness)
}

#[derive(Debug, Clone)]
pub struct Witness {
    pub formats: Vec<WitnessFormat>,
}

impl FromStr for Witness {
    type Err = String;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        if input.is_empty() {
            return Err(String::from("No satisfiable property found."));
        }

        let comment_parser = combinator::map(multi::many1(helpers::comment), |_| vec![]);
        let whole_parser = branch::alt((comment_parser, multi::many1(WitnessFormat::parse)));

        let mut witness_parser =
            combinator::map(whole_parser, |parsed| Witness { formats: parsed });

        match witness_parser(input) {
            Ok((rest, witness)) => {
                if !rest.is_empty() {
                    Err(format!("Could not parse full input. Remaining: {rest}"))
                } else {
                    Ok(witness)
                }
            }
            Err(err) => Err(err.to_string()),
        }
    }
}

enum FlowType {
    State,
    Input,
}

impl Witness {
    pub fn props_in_steps(&self) -> Vec<(PropVec, usize)> {
        let mut res = Vec::with_capacity(self.formats.len());

        for format in &self.formats {
            let props = format.header.props.clone();
            res.push((PropVec { inner: props }, format.frames.len()));
        }

        res
    }

    pub fn analyze_and_report(&self) {
        for (props, steps) in self.props_in_steps() {
            let props = props
                .inner
                .iter()
                .map(|prop| {
                    let mut prop_string = prop.to_string();

                    if matches!(&prop.property, Some(property) if property.name.is_some()) {
                        let property = prop.property.as_ref().unwrap();
                        let _ = write!(
                            &mut prop_string,
                            " named '{}' with nid: {}",
                            property.name.as_ref().unwrap(),
                            property.node
                        );
                    }

                    prop_string
                })
                .collect::<Vec<_>>()
                .join(", ");

            println!("Satisifed properties in {} steps:\n    {}\n", steps, props,);
        }

        self.analyze_input_flow();
        self.analyze_state_flow();
    }

    fn collect_assignments<'a, I>(iter: I) -> (BTreeMap<String, Vec<(u64, Assignment)>>, u64)
    where
        I: Iterator<Item = (&'a WitnessFrame, &'a Assignment)>,
    {
        let mut inputs: BTreeMap<String, Vec<(u64, Assignment)>> = BTreeMap::new();
        let mut max_step = 1;

        for (idx, (frame, input)) in iter.enumerate() {
            let step = frame.input_part.step;

            if step > max_step {
                max_step = step;
            }

            let idx_as_str = idx.to_string();
            let name = input.symbol.clone().unwrap_or(idx_as_str);

            let entry = inputs.entry(name).or_default();

            let value = input.get_value();

            match entry.last() {
                Some((_, last_assignment)) => {
                    if last_assignment.get_value() != value {
                        entry.push((step, input.clone()));
                    }
                }
                None => entry.push((step, input.clone())),
            }
        }

        (inputs, max_step)
    }

    fn print_flow(
        inputs: &BTreeMap<String, Vec<(u64, Assignment)>>,
        max_step: u64,
        flow_type: FlowType,
    ) {
        let indent = " ".repeat(4);

        let prefix = match flow_type {
            FlowType::State => "#",
            FlowType::Input => "@",
        };

        for (name, flow) in inputs.iter() {
            println!("{indent}{}: ", name);

            let largest_val = flow
                .iter()
                .map(|(_, assignment)| assignment.get_value())
                .max()
                .unwrap_or(1)
                .max(1);

            let width = max_step.ilog10() as usize + 1;
            let val_width = largest_val.ilog10() as usize + 1;

            for (idx, (step, assignment)) in flow.iter().enumerate() {
                print!("{indent}{indent}");

                if idx > 0 {
                    print!("-> ");
                } else {
                    print!("   ");
                }

                println!(
                    "{}{:>w$}: {:>v_w$} ({})",
                    prefix,
                    step,
                    assignment.get_value(),
                    assignment.kind.to_binary_string(),
                    w = width,
                    v_w = val_width,
                );
            }

            println!(
                "{indent}{indent}-> {}{:>w$}: end\n",
                prefix,
                max_step,
                w = width
            );
        }
    }

    fn analyze_input_flow(&self) {
        let frames_and_assignments =
            self.formats
                .iter()
                .flat_map(|fmt| &fmt.frames)
                .flat_map(|frame| {
                    std::iter::repeat(frame).zip(frame.input_part.model.assignments.iter())
                });

        let (inputs, max_step) = Self::collect_assignments(frames_and_assignments);

        println!("Inputs flow:");

        Self::print_flow(&inputs, max_step, FlowType::Input);
    }

    fn analyze_state_flow(&self) {
        let frames_and_assignments =
            self.formats
                .iter()
                .flat_map(|fmt| &fmt.frames)
                .flat_map(|frame| {
                    std::iter::repeat(frame).zip(
                        frame
                            .state_part
                            .iter()
                            .flat_map(|sp| sp.model.assignments.iter()),
                    )
                });

        let (inputs, max_step) = Self::collect_assignments(frames_and_assignments);

        println!("States flow:");
        Self::print_flow(&inputs, max_step, FlowType::State);
    }

    fn add_prop_names(&mut self, mut btor2_prop_names: HashMap<u64, Property>) {
        for format in &mut self.formats {
            for prop in format.header.props.iter_mut() {
                if let Some(property) = btor2_prop_names.remove(&prop.idx) {
                    prop.property = Some(property);
                }
            }
        }
    }
}
