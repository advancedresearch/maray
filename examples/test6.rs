use maray::*;
use maray::textures::channel;

fn main() {
    let color = [
        app(channel(0, 0), x(), y()),
        app(channel(0, 1), x(), y()),
        app(channel(0, 2), x(), nat(1024) - y()),
    ];
    save("test.maray", ([1024; 2], color)).unwrap();
}
