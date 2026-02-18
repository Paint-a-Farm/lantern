mod inline;
mod multi_return;

pub use inline::eliminate_temporaries;
pub use multi_return::collapse_multi_returns;
