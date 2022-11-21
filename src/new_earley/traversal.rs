use super::grammar::MatchingProductionId;
use super::input_range::InputRange;
use crate::append_vec::{append_only_vec_id, AppendOnlyVec};

append_only_vec_id!(pub(crate) TraversalId);

#[derive(Debug)]
struct Traversal<'gram> {
    lhs: &'gram crate::Term,
    matching: MatchingProductionId,
    input_range: InputRange<'gram>,
}
