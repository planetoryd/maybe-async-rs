use std::env::{Args, self};

use anyhow::Result;
use toml_edit::{self, Document, Item, Value, Array};

fn main() -> Result<()> {
    let p = "./Cargo.toml";
    let mut args = env::args();
    args.next();
    let enable: u32 = args.next().unwrap().parse()?;
    let f = std::fs::read_to_string(p).unwrap();
    let mut doc: Document = f.parse()?;
    let item: &mut Item = &mut doc["dependencies"]["maybe-async"]["features"];
    let ar = item.as_array_mut().unwrap();

    if enable == 1 {
        ar.clear();
        ar.push("is_sync");
        println!("enable sync code");
    } else {
        ar.clear();
        println!("enable async code");
    }
    std::fs::write(p, format!("{}", doc))?;

    Ok(())
}
