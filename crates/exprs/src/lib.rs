mod branch_inline;
mod inline;
mod multi_return;
mod table_fold;

pub use branch_inline::inline_branch_locals;
pub use inline::eliminate_temporaries;
pub use multi_return::collapse_multi_returns;
pub use table_fold::fold_table_constructors;
