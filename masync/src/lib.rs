use maybe_async::masy;

use futures::{
    channel::mpsc::{unbounded, UnboundedReceiver, UnboundedSender},
    Future, Sink, Stream, TryStream,
};

pub type USender<T> = masy!({std::sync::mpsc::Sender<T>} {UnboundedSender<T>});
pub type URecver<T> = masy!({std::sync::mpsc::Receiver<T>} {UnboundedReceiver<T>});

pub fn channel<T>() -> (USender<T>, URecver<T>) {
    masy!({std::sync::mpsc::channel()} {unbounded()})
}

/// Duck typing
pub type File = masy!({std::fs::File}{tokio::fs::File});

pub struct MockTryStream<T>(T);

use anyhow::Result;

impl<T> MockTryStream<T> {
    pub fn try_next(&self) -> Result<T> {
        unsafe { std::mem::zeroed() }
    }
    pub fn try_collect<C>(&self) -> Result<C> {
        unsafe { std::mem::zeroed() }
    }
}

pub use maybe_async;

impl<T> Default for MockTryStream<T> {
    fn default() -> Self {
        unsafe { std::mem::zeroed() }
    }
}
