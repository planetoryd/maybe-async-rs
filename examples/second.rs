

#[maybe_async::maybe(fn differs(arg: u64))]
async fn differs(arg: u32) {
    dbg!(arg);
}


#[maybe_async::msync]
fn main() {
    differs(2);
}

#[maybe_async::masyn]
#[tokio::main]
async fn main() {

}

