use indicatif::ProgressDrawTarget;
use owo_colors::{OwoColorize, Stream};

pub struct ProgressBar(indicatif::ProgressBar);

impl ProgressBar {
    pub fn new() -> Self {
        let pb = indicatif::ProgressBar::new(0);
        pb.set_draw_target(ProgressDrawTarget::stderr());
        Self(pb)
    }
}

impl wac_resolver::ProgressBar for ProgressBar {
    fn init(&self, count: usize) {
        self.0.reset();
        self.0.set_length(count as u64);
    }

    fn println(&self, status: &str, msg: &str) {
        self.0.suspend(|| {
            eprintln!(
                "{status:>12} {msg}",
                status = status.if_supports_color(Stream::Stderr, |text| text.bright_green())
            )
        });
    }

    fn inc(&self, delta: usize) {
        self.0.inc(delta as u64);
    }

    fn finish(&self) {
        self.0.finish_and_clear();
    }
}
