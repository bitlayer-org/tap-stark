use bitcoin::taproot::{LeafNode, LeafNodes, NodeInfo, TaprootMerkleBranch};
use bitcoin::TapNodeHash;

use super::builder::TreeBuilder;
use super::{combine_two_nodes, ScriptToEmbbed, TaptreeConcater};

#[derive(Clone, Debug)]
pub(crate) struct CompleteTaptree {
    pub root_node: NodeInfo,
    leaf_count: usize,
    leaf_indices: Vec<usize>,
}

impl CompleteTaptree {
    pub fn new(root: NodeInfo, leaf_count: usize, leaf_indices: Vec<usize>) -> Self {
        CompleteTaptree {
            root_node: root,
            leaf_count,
            leaf_indices,
        }
    }

    pub fn root(&self) -> &NodeInfo {
        
        (&self.root_node) as _
    }

    pub fn leaf_count(&self) -> usize {
        self.leaf_count
    }

    pub fn leaves(&self) -> LeafNodes {
        let nodes = self.root_node.leaf_nodes();
        nodes
    }

    pub fn get_leaf_merkle_path(&self, index: usize) -> Option<&TaprootMerkleBranch> {
        let index = self.index_map(index);
        if let Some(leaf) = self.leaves().nth(index) {
            Some(leaf.merkle_branch())
        } else {
            None
        }
    }

    fn index_map(&self, index: usize) -> usize {
        self.leaf_indices[index]
    }

    pub fn get_tapleaf(&self, index: usize) -> Option<&LeafNode> {
        let index = self.index_map(index);
        self.leaves().nth(index)
    }

    pub(crate) fn verify_inclusion_by_index(&self, index: usize) -> bool {
        let index = self.index_map(index);
        let leaf = self.get_tapleaf(index).unwrap();
        let path = self.get_leaf_merkle_path(index).unwrap();
        let mut first_node_hash = TapNodeHash::from_node_hashes(leaf.node_hash(), path[0]);
        path[1..].iter().for_each(|sibling_node| {
            first_node_hash = TapNodeHash::from_node_hashes(first_node_hash, *sibling_node);
        });

        first_node_hash == self.root().node_hash()
    }
}

pub fn verify_inclusion(root: TapNodeHash, leaf: &LeafNode) -> bool {
    let path = leaf.merkle_branch();
    let mut first_node_hash = TapNodeHash::from_node_hashes(leaf.node_hash(), path[0]);
    path[1..].iter().for_each(|sibling_node| {
        first_node_hash = TapNodeHash::from_node_hashes(first_node_hash, *sibling_node);
    });

    first_node_hash == root
}

impl TaptreeConcater for CompleteTaptree {
    fn new_with_scripts(scripts: Vec<impl ScriptToEmbbed>) -> Self {
        let mut builder = TreeBuilder::new();
        for script in scripts {
            builder.add_leaf(script.compelte_script());
        }
        builder.build_tree()
    }

    // todo: add test
    fn combine_other_script(&mut self, scripts: Vec<impl ScriptToEmbbed>) -> Self {
        let mut builder = TreeBuilder::new();
        for script in scripts {
            builder.add_leaf(script.compelte_script());
        }
        let other_tapree = builder.build_tree();
        self.combine(other_tapree)
    }

    fn combine(&self, other: impl TaptreeConcater) -> Self {
        let mut a_leaf_indices: Vec<usize> = self.get_indices().clone();
        let mut b_leaf_indices = other.get_indices().clone();

        let (combined_tree, left_first) =
            combine_two_nodes(self.get_root().clone(), other.get_root().clone()).unwrap();

        // if the left_first is ture, leaves will places as [a.leaves... ,b.leaves...]
        let taptree_indices = match left_first {
            // for swap no happen, for the merkletree index is [a_merkle_tree_indices,b_merkle_tree_indices]
            // the acctually taptree indices is [a_taptree_indices,b_taptree_indices]
            true => {
                for b_idx in b_leaf_indices.iter_mut() {
                    *b_idx += self.leaf_count();
                }
                a_leaf_indices.append(&mut b_leaf_indices);
                println!("left first {:?}", a_leaf_indices);
                a_leaf_indices
            }
            false => {
                // for swap happen, for the merkletree index is still [a_merkle_tree_indices,b_merkle_tree_indices]
                // the acctually taptree indices is [b_taptree_indices,a_taptree_indices]
                for a_idx in a_leaf_indices.iter_mut() {
                    *a_idx += other.leaf_count();
                }
                a_leaf_indices.append(&mut b_leaf_indices);

                println!("right first {:?}", a_leaf_indices);
                a_leaf_indices
            }
        };

        Self {
            root_node: combined_tree,
            leaf_count: taptree_indices.len(),
            leaf_indices: taptree_indices,
        }
    }

    fn get_indices(&self) -> &Vec<usize> {
        &self.leaf_indices
    }

    fn leaf_count(&self) -> usize {
        self.leaf_count
    }

    fn get_root(&self) -> &NodeInfo {
        &self.root_node
    }

    fn get_leaf_proof(&self, index: usize) -> (LeafNode, TaprootMerkleBranch) {
        let leaf = self.get_tapleaf(index).unwrap();
        let path = self.get_leaf_merkle_path(index).unwrap();
        (leaf.clone(), path.clone())
    }
}

#[cfg(test)]
mod tests {

    use bitcoin::opcodes::all::OP_ADD;
    use bitcoin::{Script, ScriptBuf};
    use bitcoin_script::{define_pushable, script};

    use super::{CompleteTaptree, TaptreeConcater};
    define_pushable!();

    #[test]
    fn test_build_tree() {
        let nums = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15u32];
        // let nums = vec![0,1,2,3,4,5,6,7,8,10,11,12,13,14,15u32];
        // let nums = vec![1u32];
        let scripts = nums
            .iter()
            .map(|index| {
                script! {
                    {*index}
                    OP_ADD

                }
            })
            .collect::<Vec<ScriptBuf>>();

        let a_tree = CompleteTaptree::new_with_scripts(scripts);

        assert_eq!(a_tree.leaf_count(), 16);

        let ap = a_tree.get_tapleaf(0).unwrap();
        assert_eq!(
            ap.leaf().as_script().unwrap().0.as_bytes(),
            script! { {0} OP_ADD}.as_bytes()
        );

        let ap = a_tree.get_tapleaf(6).unwrap();
        assert_eq!(
            ap.leaf().as_script().unwrap().0.as_bytes(),
            script! { {6} OP_ADD}.as_bytes()
        );

        let indices = a_tree.get_indices();
        println!("{:?}", indices);
        // let ap = a_tree.get_tapleaf(8).unwrap();
        // println!("ap {:?}",ap);

        for (query_index, value) in nums.iter().enumerate() {
            println!("query_index {:?}, value: {:?}", query_index, value);
            let ap = a_tree.get_tapleaf(query_index).unwrap();
            assert!(a_tree.verify_inclusion_by_index(query_index));
            assert_eq!(
                ap.leaf().as_script().unwrap().0.as_bytes(),
                script! { {*value} OP_ADD}.as_bytes()
            );
        }
    }

    #[test]
    fn test_combine_tree() {
        let nums = vec![0, 1, 2, 3, 4, 5, 6, 7u32];
        let scripts = nums
            .iter()
            .map(|index| {
                script! {
                    {*index}
                    OP_ADD

                }
            })
            .collect::<Vec<ScriptBuf>>();

        let a_tree = CompleteTaptree::new_with_scripts(scripts);

        for (query_index, value) in nums.iter().enumerate() {
            let ap = a_tree.get_tapleaf(query_index).unwrap();
            assert_eq!(
                ap.leaf().as_script().unwrap().0.as_bytes(),
                script! { {*value} OP_ADD}.as_bytes()
            );
        }

        let b_nums = vec![8, 9, 10, 11, 12, 13, 14, 15u32];
        let b_scripts = b_nums
            .iter()
            .map(|index| {
                script! {
                    {*index}
                    OP_ADD

                }
            })
            .collect::<Vec<ScriptBuf>>();
        let b_tree = CompleteTaptree::new_with_scripts(b_scripts);
        for (query_index, value) in b_nums.iter().enumerate() {
            let ap = b_tree.get_tapleaf(query_index).unwrap();
            assert_eq!(
                ap.leaf().as_script().unwrap().0.as_bytes(),
                script! { {*value} OP_ADD}.as_bytes()
            );
        }

        // combine tree with right-first
        let c_tree = a_tree.clone().combine(b_tree.clone());
        println!("a_tree: {:?}", a_tree.leaf_indices);
        println!("b_tree: {:?}", b_tree.leaf_indices);
        println!("c_tree: {:?}", c_tree.leaf_indices);
        let expect_nums = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15u32];
        for (query_index, value) in expect_nums.iter().enumerate() {
            println!("query_index {:?}, value: {:?}", query_index, value);
            let ap = c_tree.get_tapleaf(query_index).unwrap();
            println!("{:?}", ap.leaf().as_script().unwrap());
            assert!(c_tree.verify_inclusion_by_index(query_index));
            assert_eq!(
                ap.leaf().as_script().unwrap().0.as_bytes(),
                script! { {*value} OP_ADD}.as_bytes()
            );
        }

        // combine tree with left-first
        let c_tree = b_tree.clone().combine(a_tree.clone());

        println!("a_tree: {:?}", a_tree.leaf_indices);
        println!("b_tree: {:?}", b_tree.leaf_indices);
        println!("c_tree: {:?}", c_tree.leaf_indices);
        let expect_nums = vec![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7u32];
        for (query_index, value) in expect_nums.iter().enumerate() {
            println!("query_index {:?}, value: {:?}", query_index, value);
            let ap = c_tree.get_tapleaf(query_index).unwrap();
            println!("{:?}", ap.leaf().as_script().unwrap());
            assert!(c_tree.verify_inclusion_by_index(query_index));
            assert_eq!(
                ap.leaf().as_script().unwrap().0.as_bytes(),
                script! { {*value} OP_ADD}.as_bytes()
            );
        }
    }

    #[test]
    fn test_combine_with_different_depth() {
        let nums = vec![0, 1, 2, 3, 4, 5, 6, 7u32];
        let scripts = nums
            .iter()
            .map(|index| {
                script! {
                    {*index}
                    OP_ADD

                }
            })
            .collect::<Vec<ScriptBuf>>();

        let a_tree = CompleteTaptree::new_with_scripts(scripts);

        for (query_index, value) in nums.iter().enumerate() {
            let ap = a_tree.get_tapleaf(query_index).unwrap();
            assert_eq!(
                ap.leaf().as_script().unwrap().0.as_bytes(),
                script! { {*value} OP_ADD}.as_bytes()
            );
        }

        let b_nums = vec![8, 9, 10, 11u32];
        let b_scripts = b_nums
            .iter()
            .map(|index| {
                script! {
                    {*index}
                    OP_ADD

                }
            })
            .collect::<Vec<ScriptBuf>>();
        let b_tree = CompleteTaptree::new_with_scripts(b_scripts);
        for (query_index, value) in b_nums.iter().enumerate() {
            let ap = b_tree.get_tapleaf(query_index).unwrap();
            assert_eq!(
                ap.leaf().as_script().unwrap().0.as_bytes(),
                script! { {*value} OP_ADD}.as_bytes()
            );
        }

        // combine tree with right-first
        let c_tree = a_tree.clone().combine(b_tree.clone());
        println!("a_tree: {:?}", a_tree.leaf_indices);
        println!("b_tree: {:?}", b_tree.leaf_indices);
        println!("c_tree: {:?}", c_tree.leaf_indices);
        let expect_nums = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11u32];
        for (query_index, value) in expect_nums.iter().enumerate() {
            println!("query_index {:?}, value: {:?}", query_index, value);
            let ap = c_tree.get_tapleaf(query_index).unwrap();
            println!("{:?}", ap.leaf().as_script().unwrap());
            assert!(c_tree.verify_inclusion_by_index(query_index));
            assert_eq!(
                ap.leaf().as_script().unwrap().0.as_bytes(),
                script! { {*value} OP_ADD}.as_bytes()
            );
        }

        // combine tree with left-first
        let c_tree = b_tree.clone().combine(a_tree.clone());

        println!("a_tree: {:?}", a_tree.leaf_indices);
        println!("b_tree: {:?}", b_tree.leaf_indices);
        println!("c_tree: {:?}", c_tree.leaf_indices);
        let expect_nums = vec![8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7u32];
        for (query_index, value) in expect_nums.iter().enumerate() {
            println!("query_index {:?}, value: {:?}", query_index, value);
            let ap = c_tree.get_tapleaf(query_index).unwrap();
            println!("{:?}", ap.leaf().as_script().unwrap());
            assert!(c_tree.verify_inclusion_by_index(query_index));
            assert_eq!(
                ap.leaf().as_script().unwrap().0.as_bytes(),
                script! { {*value} OP_ADD}.as_bytes()
            );
        }
    }
}
