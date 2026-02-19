mod inline;
mod multi_return;
mod table_fold;

pub use inline::eliminate_temporaries;
pub use multi_return::collapse_multi_returns;
pub use table_fold::fold_table_constructors;
