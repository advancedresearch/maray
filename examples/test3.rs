use maray::*;
use maray::semantics::*;
use maray::partial_red::*;
use maray::memory_manager::MemoryManager;

fn main() {
    let c = PartialRed;
    let mut a = c.decorate(sub(div(nat(2), nat(5)), recip(nat(3))));
    println!("{}", a);

    let ref mut mem = MemoryManager::new(10_000);
    loop {
        let old_a = a.clone();
        a = c.propagate(a, mem);
        if a != old_a {
            println!("{}", a);
        } else {break}
    }
    println!("{}", decor_inner(&a).simplify(mem));
}
