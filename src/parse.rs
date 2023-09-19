use proc_macro2::{Group, Span};
use syn::{
    parse::{discouraged::Speculative, Parse, ParseStream, Result},
    Attribute, Error, ItemFn, ItemImpl, ItemStatic, ItemTrait, TraitItem, TraitItemMethod,
};

pub enum Item {
    Trait(ItemTrait),
    Impl(ItemImpl),
    Fn(ItemFn),
    Static(ItemStatic),
    TraitMethod(TraitItemMethod),
}

macro_rules! fork {
    ($fork:ident = $input:ident) => {{
        $fork = $input.fork();
        &$fork
    }};
}

#[derive(Debug)]
pub struct GroupPair {
    pub left: Group,
    pub right: Group,
}

impl Parse for GroupPair {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            left: input.parse()?,
            right: input.parse()?,
        })
    }
}

impl Parse for Item {
    fn parse(input: ParseStream) -> Result<Self> {
        let attrs = input.call(Attribute::parse_outer)?;
        let mut fork;
        let item = if let Some(mut item) = fork!(fork = input).parse::<ItemImpl>().ok() {
            item.attrs = attrs;
            Item::Impl(item)
        } else if let Some(mut item) = fork!(fork = input).parse::<ItemTrait>().ok() {
            item.attrs = attrs;
            Item::Trait(item)
        } else if let Some(mut item) = fork!(fork = input).parse::<ItemFn>().ok() {
            item.attrs = attrs;
            Item::Fn(item)
        } else if let Some(mut item) = fork!(fork = input).parse::<TraitItemMethod>().ok() {
            item.attrs = attrs;
            Item::TraitMethod(item)
        } else if let Some(mut item) = fork!(fork = input).parse::<ItemStatic>().ok() {
            item.attrs = attrs;
            Item::Static(item)
        } else {
            return Err(Error::new(
                Span::call_site(),
                "expected trait impl, trait or fn",
            ));
        };
        input.advance_to(&fork);
        Ok(item)
    }
}
