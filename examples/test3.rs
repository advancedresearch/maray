use maray::*;
use maray::semantics::*;
use maray::partial_red::*;

fn main() {
    let c = PartialRed;
    let mut a = c.decorate(sub(div(nat(2), nat(5)), recip(nat(3))));
    println!("{}", a);

    loop {
        let old_a = a.clone();
        a = c.propagate(a);
        if a != old_a {
            println!("{}", a);
        } else {break}
    }
    println!("{}", decor_inner(&a).simplify());
}
