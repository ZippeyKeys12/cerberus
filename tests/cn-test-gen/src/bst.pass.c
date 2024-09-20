#include "stdlib.h"

struct int_tree {
    int key;
    struct int_tree* left;
    struct int_tree* right;
};

/*@
    datatype binary_tree {
        Tree_Leaf {},
        Tree_Node { i32 key, datatype binary_tree left, datatype binary_tree right }
    }
    predicate (datatype binary_tree) IntTree(pointer p) {
        if (is_null(p)) {
            return Tree_Leaf {};
        } else {
            take n = Owned<struct int_tree>(p);
            let tmp1 = n.left;
            take l = IntTree(tmp1);
            let tmp2 = n.right;
            take r = IntTree(tmp2);
            return Tree_Node { key: n.key, left: l, right: r };
        }
    }
@*/

struct int_tree* mallocIntTree()
    /*@ trusted;
        requires
            true;
        ensures
            take T = Block<struct int_tree>(return);
            !is_null(return);
    @*/
{
    return malloc(sizeof(struct int_tree));
}

void freeIntTree(struct int_tree* p)
/*@ trusted;
    requires
        take T = Block<struct int_tree>(p);
    ensures
        true;
@*/
{
    free(p);
}

void deepFreeIntTree(struct int_tree* p)
/*@
    requires
        take T = IntTree(p);
@*/
{
    if (p == 0) {
        return;
    }

    deepFreeIntTree(p->left);
    deepFreeIntTree(p->right);
    freeIntTree(p);
}

struct int_tree* emptyTree()
    /*@
    ensures
        take T = IntTree(return);
        T == Tree_Leaf {};
    @*/
{
    return 0;
}

struct int_tree* newNode(int key)
    /*@
        ensures
            take T = IntTree(return);
            T == Tree_Node {
                key: key,
                left: Tree_Leaf {},
                right: Tree_Leaf {}
            };
    @*/
{
    struct int_tree* p = mallocIntTree();
    p->key = key;
    p->left = 0;
    p->right = 0;
    return p;
}

struct int_tree* deepCopyRecursive(struct int_tree* p)
    /*@
        requires
            take T = IntTree(p);
        ensures
            take T_ = IntTree(p);
            T == T_;
            take T2 = IntTree(return);
            T == T2;
    @*/
{
    if (p == 0) {
        return 0;
    }

    struct int_tree* q = mallocIntTree();
    q->key = p->key;
    q->left = deepCopyRecursive(p->left);
    q->right = deepCopyRecursive(p->right);
    return q;
}

// Here's a definition.
 /*@
     predicate (datatype binary_tree) IntBst(pointer p) {
         if (is_null(p)) {
             return Tree_Leaf {};
         } else {
             take n = Owned<struct int_tree>(p);
             let tmp1 = n.left;
             take l = IntBst(tmp1);
             assert (match l {
                 Tree_Leaf {} => { true }
                 Tree_Node {
                     key: k,
                     left: _,
                     right: _
                 } => { k < n.key }
             });
             let tmp2 = n.right;
             take r = IntBst(tmp2);
             assert (match r {
                 Tree_Leaf {} => { true }
                 Tree_Node {
                     key: k,
                     left: _,
                     right: _
                 } => { n.key < k }
             });
             return Tree_Node { key: n.key, left: l, right: r };
         }
     }
 @*/
 // And here's one that reuses our `IntTree` predicate.
 /*@
     function [rec] (boolean) isSortedTree(datatype binary_tree tree) {
         match tree {
             Tree_Leaf {} => { true }
             Tree_Node {
                 key: k,
                 left: l,
                 right: r
             } => {
                 (match l {
                     Tree_Leaf {} => { true }
                     Tree_Node {
                         key: k_l,
                         left: _,
                         right: _
                     } => {
                         k_l < k && isSortedTree(l)
                     }
                 }) &&
                 (match r {
                     Tree_Leaf {} => { true }
                     Tree_Node {
                         key: k_r,
                         left: _,
                         right: _
                     } => {
                         k < k_r && isSortedTree(r)
                     }
                 })
             }
         }
     }
     predicate (datatype binary_tree) IntBstAlt(pointer p) {
         take T = IntTree(p);
         assert(isSortedTree(T));
         return T;
     }
 @*/

 /*@
     function [rec] (datatype binary_tree) insert(datatype binary_tree tree, i32 to_insert) {
         match tree {
             Tree_Leaf {} => {
                 Tree_Node {
                     key: to_insert,
                     left: Tree_Leaf {},
                     right: Tree_Leaf {}
                 }
             }
             Tree_Node {
                 key: k,
                 left: l,
                 right: r
             } => {
                 if (to_insert < k) {
                     Tree_Node {
                         key: k,
                         left: insert(l, to_insert),
                         right: r
                     }
                 } else {
                     if (k < to_insert) {
                         Tree_Node {
                             key: k,
                             left: l,
                             right: insert(r, to_insert)
                         }
                     } else {
                         tree
                     }
                 }
             }
         }
     }
 @*/

struct int_tree* insert(struct int_tree* tree, int key)
    /*@
    requires
        take T1 = IntBst(tree);
    ensures
        take T2 = IntBst(return);
        T2 == insert(T1, key);
    @*/
{
    if (tree == 0) {
        struct int_tree* ret = mallocIntTree();
        ret->key = key;
        ret->left = 0;
        ret->right = 0;

        /*@ unfold insert(T1, key); @*/
        return ret;
    }

    if (key < tree->key) {
        tree->left = insert(tree->left, key);
    }
    else if (tree->key < key) {
        tree->right = insert(tree->right, key);
    }
    return tree;
}

/*@
    lemma BstIsTree(pointer p)
    requires
        take T = IntBst(p);
    ensures
        take T2 = IntTree(p);
@*/
