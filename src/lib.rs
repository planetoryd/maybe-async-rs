//!
//! # Maybe-Async Procedure Macro
//!
//! **Why bother writing similar code twice for blocking and async code?**
//!
//! [![Build Status](https://github.com/fMeow/maybe-async-rs/workflows/CI%20%28Linux%29/badge.svg?branch=main)](https://github.com/fMeow/maybe-async-rs/actions)
//! [![MIT licensed](https://img.shields.io/badge/license-MIT-blue.svg)](./LICENSE)
//! [![Latest Version](https://img.shields.io/crates/v/maybe-async.svg)](https://crates.io/crates/maybe-async)
//! [![maybe-async](https://docs.rs/maybe-async/badge.svg)](https://docs.rs/maybe-async)
//!
//! When implementing both sync and async versions of API in a crate, most API
//! of the two version are almost the same except for some async/await keyword.
//!
//! `maybe-async` help unifying async and sync implementation by **procedural
//! macro**.
//! - Write async code with normal `async`, `await`, and let `maybe_async`
//!   handles
//! those `async` and `await` when you need a blocking code.
//! - Switch between sync and async by toggling `is_sync` feature gate in
//!   `Cargo.toml`.
//! - use `must_be_async` and `must_be_sync` to keep code in specified version
//! - use `async_impl` and `sync_impl` to only compile code block on specified
//!   version
//! - A handy macro to unify unit test code is also provided.
//!
//! These procedural macros can be applied to the following codes:
//! - trait item declaration
//! - trait implmentation
//! - function definition
//! - struct definition
//!
//! **RECOMMENDATION**: Enable **resolver ver2** in your crate, which is
//! introduced in Rust 1.51. If not, two crates in dependency with conflict
//! version (one async and another blocking) can fail complilation.
//!
//!
//! ## Motivation
//!
//! The async/await language feature alters the async world of rust.
//! Comparing with the map/and_then style, now the async code really resembles
//! sync version code.
//!
//! In many crates, the async and sync version of crates shares the same API,
//! but the minor difference that all async code must be awaited prevent the
//! unification of async and sync code. In other words, we are forced to write
//! an async and an sync implementation repectively.
//!
//! ## Macros in Detail
//!
//! `maybe-async` offers 4 set of attribute macros: `maybe_async`,
//! `sync_impl`/`async_impl`, `must_be_sync`/`must_be_async`,  and `test`.
//!
//! To use `maybe-async`, we must know which block of codes is only used on
//! blocking implementation, and which on async. These two implementation should
//! share the same function signatures except for async/await keywords, and use
//! `sync_impl` and `async_impl` to mark these implementation.
//!
//! Use `maybe_async` macro on codes that share the same API on both async and
//! blocking code except for async/await keywords. And use feature gate
//! `is_sync` in `Cargo.toml` to toggle between async and blocking code.
//!
//! - `maybe_async`
//!
//!     Offers a unified feature gate to provide sync and async conversion on
//!     demand by feature gate `is_sync`, with **async first** policy.
//!
//!     Want to keep async code? add `maybe_async` in dependencies with default
//!     features, which means `maybe_async` is the same as `must_be_async`:
//!
//!     ```toml
//!     [dependencies]
//!     maybe_async = "0.2"
//!     ```
//!
//!     Wanna convert async code to sync? Add `maybe_async` to dependencies with
//!     an `is_sync` feature gate. In this way, `maybe_async` is the same as
//!     `must_be_sync`:
//!
//!     ```toml
//!     [dependencies]
//!     maybe_async = { version = "0.2", features = ["is_sync"] }
//!     ```
//!
//!     Not all async traits need futures that are `dyn Future + Send`.
//!     To avoid having "Send" and "Sync" bounds placed on the async trait
//!     methods, invoke the maybe_async macro as #[maybe_async(?Send)] on both
//!     the trait and the impl blocks.
//!
//!
//! - `must_be_async`
//!
//!     **Keep async**. Add `async_trait` attribute macro for trait declaration
//!     or implementation to bring async fn support in traits.
//!
//!     To avoid having "Send" and "Sync" bounds placed on the async trait
//!     methods, invoke the maybe_async macro as #[must_be_async(?Send)].
//!
//! - `must_be_sync`
//!
//!     **Convert to sync code**. Convert the async code into sync code by
//!     removing all `async move`, `async` and `await` keyword
//!
//!
//! - `sync_impl`
//!
//!     An sync implementation should on compile on blocking implementation and
//! must     simply disappear when we want async version.
//!
//!     Although most of the API are almost the same, there definitely come to a
//!     point when the async and sync version should differ greatly. For
//!     example, a MongoDB client may use the same API for async and sync
//!     verison, but the code to actually send reqeust are quite different.
//!
//!     Here, we can use `sync_impl` to mark a synchronous implementation, and a
//!     sync implementation shoule disappear when we want async version.
//!
//! - `async_impl`
//!
//!     An async implementation should on compile on async implementation and
//! must     simply disappear when we want sync version.
//!
//!     To avoid having "Send" and "Sync" bounds placed on the async trait
//!     methods, invoke the maybe_async macro as #[async_impl(?Send)].
//!
//!
//! - `test`
//!
//!     Handy macro to unify async and sync **unit and e2e test** code.
//!
//!     You can specify the condition to compile to sync test code
//!     and also the conditions to compile to async test code with given test
//!     macro, e.x. `tokio::test`, `async_std::test` and etc. When only sync
//!     condition is specified,the test code only compiles when sync condition
//!     is met.
//!
//!     ```rust
//!     # #[maybe_async::maybe_async]
//!     # async fn async_fn() -> bool {
//!     #    true
//!     # }
//!
//!     ##[maybe_async::test(
//!         feature="is_sync",
//!         async(
//!             all(not(feature="is_sync"), feature="async_std"),
//!             async_std::test
//!         ),
//!         async(
//!             all(not(feature="is_sync"), feature="tokio"),
//!             tokio::test
//!         )
//!     )]
//!     async fn test_async_fn() {
//!         let res = async_fn().await;
//!         assert_eq!(res, true);
//!     }
//!     ```
//!
//! ## What's Under the Hook
//!
//! `maybe-async` compiles your code in different way with the `is_sync` feature
//! gate. It remove all `await` and `async` keywords in your code under
//! `maybe_async` macro and conditionally compiles codes under `async_impl` and
//! `sync_impl`.
//!
//! Here is an detailed example on what's going on whe the `is_sync` feature
//! gate set or not.
//!
//! ```rust
//! #[maybe_async::maybe_async(?Send)]
//! trait A {
//!     async fn async_fn_name() -> Result<(), ()> {
//!         Ok(())
//!     }
//!     fn sync_fn_name() -> Result<(), ()> {
//!         Ok(())
//!     }
//! }
//!
//! struct Foo;
//!
//! #[maybe_async::maybe_async(?Send)]
//! impl A for Foo {
//!     async fn async_fn_name() -> Result<(), ()> {
//!         Ok(())
//!     }
//!     fn sync_fn_name() -> Result<(), ()> {
//!         Ok(())
//!     }
//! }
//!
//! #[maybe_async::maybe_async]
//! async fn maybe_async_fn() -> Result<(), ()> {
//!     let a = Foo::async_fn_name().await?;
//!
//!     let b = Foo::sync_fn_name()?;
//!     Ok(())
//! }
//! ```
//!
//! When `maybe-async` feature gate `is_sync` is **NOT** set, the generated code
//! is async code:
//!
//! ```rust
//! // Compiled code when `is_sync` is toggled off.
//! #[async_trait::async_trait(?Send)]
//! trait A {
//!     async fn maybe_async_fn_name() -> Result<(), ()> {
//!         Ok(())
//!     }
//!     fn sync_fn_name() -> Result<(), ()> {
//!         Ok(())
//!     }
//! }
//!
//! struct Foo;
//!
//! #[async_trait::async_trait(?Send)]
//! impl A for Foo {
//!     async fn maybe_async_fn_name() -> Result<(), ()> {
//!         Ok(())
//!     }
//!     fn sync_fn_name() -> Result<(), ()> {
//!         Ok(())
//!     }
//! }
//!
//! async fn maybe_async_fn() -> Result<(), ()> {
//!     let a = Foo::maybe_async_fn_name().await?;
//!     let b = Foo::sync_fn_name()?;
//!     Ok(())
//! }
//! ```
//!
//! When `maybe-async` feature gate `is_sync` is set, all async keyword is
//! ignored and yields a sync version code:
//!
//! ```rust
//! // Compiled code when `is_sync` is toggled on.
//! trait A {
//!     fn maybe_async_fn_name() -> Result<(), ()> {
//!         Ok(())
//!     }
//!     fn sync_fn_name() -> Result<(), ()> {
//!         Ok(())
//!     }
//! }
//!
//! struct Foo;
//!
//! impl A for Foo {
//!     fn maybe_async_fn_name() -> Result<(), ()> {
//!         Ok(())
//!     }
//!     fn sync_fn_name() -> Result<(), ()> {
//!         Ok(())
//!     }
//! }
//!
//! fn maybe_async_fn() -> Result<(), ()> {
//!     let a = Foo::maybe_async_fn_name()?;
//!     let b = Foo::sync_fn_name()?;
//!     Ok(())
//! }
//! ```
//!
//! ## Examples
//!
//! ### rust client for services
//!
//! When implementing rust client for any services, like awz3. The higher level
//! API of async and sync version is almost the same, such as creating or
//! deleting a bucket, retrieving an object and etc.
//!
//! The example `service_client` is a proof of concept that `maybe_async` can
//! actually free us from writing almost the same code for sync and async. We
//! can toggle between a sync AWZ3 client and async one by `is_sync` feature
//! gate when we add `maybe-async` to dependency.
//!
//!
//! # License
//! MIT

extern crate proc_macro;

use proc_macro::TokenStream;

use proc_macro2::{Group, Span, TokenStream as TokenStream2};
use quote::quote;
use syn::{
    parse_macro_input, punctuated::Punctuated, spanned::Spanned, AttributeArgs, Error, ImplItem,
    Lit, Meta, NestedMeta, Signature, TraitItem,
};

use crate::{
    parse::{GroupPair, Item},
    visit::AsyncAwaitRemoval,
};

mod parse;
mod visit;

fn convert_async(input: TokenStream) -> TokenStream {
    input
}

fn convert_sync(input: &mut Item, sig: Option<Signature>) -> TokenStream {
    match input {
        Item::Mod(item) => {
            if item.content.is_none() {
                Error::new(item.span(), "useless annonation").to_compile_error()
            } else {
                proc_mod(item);
                AsyncAwaitRemoval.remove_async_await(quote!(#item))
            }
        }
        Item::Impl(item) => {
            for inner in &mut item.items {
                process_impl(inner);
            }
            AsyncAwaitRemoval.remove_async_await(quote!(#item))
        }
        Item::Trait(item) => {
            for inner in &mut item.items {
                process_trait_item(inner);
            }
            AsyncAwaitRemoval.remove_async_await(quote!(#item))
        }
        Item::Fn(item) => {
            if item.sig.asyncness.is_some() {
                item.sig.asyncness = None;
            }
            if let Some(sig) = sig {
                item.sig = sig;
            }
            AsyncAwaitRemoval.remove_async_await(quote!(#item))
        }
        Item::TraitMethod(item) => {
            if item.sig.asyncness.is_some() {
                item.sig.asyncness = None;
            }
            if let Some(sig) = sig {
                item.sig = sig;
            }
            quote!(#item)
        }
        Item::Static(item) => AsyncAwaitRemoval.remove_async_await(quote!(#item)),
    }
    .into()
}

fn proc_mod(item: &mut syn::ItemMod) {
    if let Some((b, m)) = &mut item.content {
        for item in m {
            match item {
                syn::Item::Impl(imp) => {
                    for inner in &mut imp.items {
                        process_impl(inner);
                    }
                }
                syn::Item::Fn(item) => {
                    if item.sig.asyncness.is_some() {
                        item.sig.asyncness = None;
                    }
                }
                syn::Item::Trait(item) => {
                    for inner in &mut item.items {
                        process_trait_item(inner);
                    }
                }
                syn::Item::Mod(item) => {
                    proc_mod(item);
                }
                _ => (),
            }
        }
    }
}

fn process_trait_item(inner: &mut TraitItem) {
    if let TraitItem::Method(ref mut method) = inner {
        if method.sig.asyncness.is_some() {
            method.sig.asyncness = None;
        }
    }
}

fn process_impl(inner: &mut ImplItem) {
    if let ImplItem::Method(ref mut method) = inner {
        if method.sig.asyncness.is_some() {
            method.sig.asyncness = None;
        }
    }
}

/// maybe_async(fn signature for sync goes here)
/// Rewrites the item into sync/async according to cfg.
#[proc_macro_attribute]
pub fn maybe(args: TokenStream, input: TokenStream) -> TokenStream {
    let token = if cfg!(feature = "is_sync") {
        let mut item = parse_macro_input!(input as Item);
        let sig = if args.is_empty() {
            None
        } else {
            let sig = parse_macro_input!(args as Signature);
            Some(sig)
        };
        convert_sync(&mut item, sig)
    } else {
        convert_async(input)
    };
    token.into()
}

/// Maybe async ( { sync code } { async code } )
#[proc_macro]
pub fn masy(input: TokenStream) -> TokenStream {
    let k = parse_macro_input!(input as GroupPair);
    let token = if cfg!(feature = "is_sync") {
        k.left.stream()
    } else {
        k.right.stream()
    };
    token.into()
}

/// convert marked async code to sync code
#[proc_macro_attribute]
pub fn to_sync(args: TokenStream, input: TokenStream) -> TokenStream {
    let mut item = parse_macro_input!(input as Item);
    let sig = if args.is_empty() {
        None
    } else {
        let sig = parse_macro_input!(args as Signature);
        Some(sig)
    };
    convert_sync(&mut item, sig).into()
}

/// mark sync implementation
///
/// only compiled when `is_sync` feature gate is set.
/// When `is_sync` is not set, marked code is removed.
#[proc_macro_attribute]
pub fn msync(_args: TokenStream, input: TokenStream) -> TokenStream {
    let input = TokenStream2::from(input);
    let token = if cfg!(feature = "is_sync") {
        quote!(#input)
    } else {
        quote!()
    };
    token.into()
}

#[allow(dead_code)]
/// An indicator for you.
#[cfg(feature = "is_sync")]
type Test = ();

/// mark async implementation
///
/// only compiled when `is_sync` feature gate is not set.
/// When `is_sync` is set, marked code is removed.
#[proc_macro_attribute]
pub fn masyn(_args: TokenStream, input: TokenStream) -> TokenStream {
    let token = if cfg!(feature = "is_sync") {
        quote!().into()
    } else {
        convert_async(input)
    };
    token.into()
}

macro_rules! match_nested_meta_to_str_lit {
    ($t:expr) => {
        match $t {
            NestedMeta::Lit(lit) => {
                match lit {
                    Lit::Str(s) => {
                        s.value().parse::<TokenStream2>().unwrap()
                    }
                    _ => {
                        return syn::Error::new(lit.span(), "expected meta or string literal").to_compile_error().into();
                    }
                }
            }
            NestedMeta::Meta(meta) => quote!(#meta)
        }
    };
}

/// Handy macro to unify test code of sync and async code
///
/// Since the API of both sync and async code are the same,
/// with only difference that async functions must be awaited.
/// So it's tedious to write unit sync and async respectively.
///
/// This macro helps unify the sync and async unit test code.
/// Pass the condition to treat test code as sync as the first
/// argument. And specify the condition when to treat test code
/// as async and the lib to run async test, e.x. `async-std::test`,
/// `tokio::test`, or any valid attribute macro.
///
/// **ATTENTION**: do not write await inside a assert macro
///
/// - Examples
///
/// ```rust
/// #[maybe_async::maybe_async]
/// async fn async_fn() -> bool {
///     true
/// }
///
/// #[maybe_async::test(
///     // when to treat the test code as sync version
///     feature="is_sync",
///     // when to run async test
///     async(all(not(feature="is_sync"), feature="async_std"), async_std::test),
///     // you can specify multiple conditions for different async runtime
///     async(all(not(feature="is_sync"), feature="tokio"), tokio::test)
/// )]
/// async fn test_async_fn() {
///     let res = async_fn().await;
///     assert_eq!(res, true);
/// }
///
/// // Only run test in sync version
/// #[maybe_async::test(feature = "is_sync")]
/// async fn test_sync_fn() {
///     let res = async_fn().await;
///     assert_eq!(res, true);
/// }
/// ```
///
/// The above code is transcripted to the following code:
///
/// ```rust
/// # use maybe_async::{must_be_async, must_be_sync, sync_impl};
/// # #[maybe_async::maybe_async]
/// # async fn async_fn() -> bool { true }
///
/// // convert to sync version when sync condition is met, keep in async version when corresponding
/// // condition is met
/// #[cfg_attr(feature = "is_sync", must_be_sync, test)]
/// #[cfg_attr(
///     all(not(feature = "is_sync"), feature = "async_std"),
///     must_be_async,
///     async_std::test
/// )]
/// #[cfg_attr(
///     all(not(feature = "is_sync"), feature = "tokio"),
///     must_be_async,
///     tokio::test
/// )]
/// async fn test_async_fn() {
///     let res = async_fn().await;
///     assert_eq!(res, true);
/// }
///
/// // force converted to sync function, and only compile on sync condition
/// #[cfg(feature = "is_sync")]
/// #[test]
/// fn test_sync_fn() {
///     let res = async_fn();
///     assert_eq!(res, true);
/// }
/// ```
#[proc_macro_attribute]
pub fn test(args: TokenStream, input: TokenStream) -> TokenStream {
    let attr_args = parse_macro_input!(args as AttributeArgs);
    let input = TokenStream2::from(input);
    if attr_args.len() < 1 {
        return syn::Error::new(
            Span::call_site(),
            "Arguments cannot be empty, at least specify the condition for sync code",
        )
        .to_compile_error()
        .into();
    }

    // The first attributes indicates sync condition
    let sync_cond = match_nested_meta_to_str_lit!(attr_args.first().unwrap());
    let mut ts = quote!(#[cfg_attr(#sync_cond, maybe_async::must_be_sync, test)]);

    // The rest attributes indicates async condition and async test macro
    // only accepts in the forms of `async(cond, test_macro)`, but `cond` and
    // `test_macro` can be either meta attributes or string literal
    let mut async_token = Vec::new();
    let mut async_conditions = Vec::new();
    for async_meta in attr_args.into_iter().skip(1) {
        match async_meta {
            NestedMeta::Meta(meta) => match meta {
                Meta::List(list) => {
                    let name = list.path.segments[0].ident.to_string();
                    if name.ne("async") {
                        return syn::Error::new(
                            list.path.span(),
                            format!("Unknown path: `{}`, must be `async`", name),
                        )
                        .to_compile_error()
                        .into();
                    }
                    if list.nested.len() == 2 {
                        let async_cond =
                            match_nested_meta_to_str_lit!(list.nested.first().unwrap());
                        let async_test = match_nested_meta_to_str_lit!(list.nested.last().unwrap());
                        let attr = quote!(
                            #[cfg_attr(#async_cond, maybe_async::must_be_async, #async_test)]
                        );
                        async_conditions.push(async_cond);
                        async_token.push(attr);
                    } else {
                        let msg = format!(
                            "Must pass two metas or string literals like `async(condition, \
                             async_test_macro)`, you passed {} metas.",
                            list.nested.len()
                        );
                        return syn::Error::new(list.span(), msg).to_compile_error().into();
                    }
                }
                _ => {
                    return syn::Error::new(
                        meta.span(),
                        "Must be list of metas like: `async(condition, async_test_macro)`",
                    )
                    .to_compile_error()
                    .into();
                }
            },
            NestedMeta::Lit(lit) => {
                return syn::Error::new(
                    lit.span(),
                    "Must be list of metas like: `async(condition, async_test_macro)`",
                )
                .to_compile_error()
                .into();
            }
        };
    }

    async_token.into_iter().for_each(|t| ts.extend(t));
    ts.extend(quote!( #input ));
    if !async_conditions.is_empty() {
        quote! {
            #[cfg(any(#sync_cond, #(#async_conditions),*))]
            #ts
        }
    } else {
        quote! {
            #[cfg(#sync_cond)]
            #ts
        }
    }
    .into()
}
