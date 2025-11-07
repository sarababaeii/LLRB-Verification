include "GhostFunction.dfy"

/* Check if t is LLRB */
predicate isLLRB (t: LLRB)
{
    match t
        case Empty            => true
        case Node(l, c, k, r) => isLLRB(l) &&
                                 isLLRB(r) &&
                                 balanced(t) &&
                                 BST(t) &&
                                 goodColor(t)
}

/* Not check root color, i.e can have two consecutive red edges. */
predicate weakLLRB (t: LLRB)
{
   match t
        case Empty            => true
        case Node(l, c, k, r) => isLLRB(l) &&
                                 isLLRB(r) &&
                                 balanced(t) &&
                                 BST(t) &&
                                 (color(r) == Red ==> color(l) == Red)
}

/* BST proterity: x is grater than all node in left subtree and less than all nodes in right subtree */
predicate BST_Root(l: LLRB, x: int, r: LLRB) 
{
   (forall z :: z in tset(l) ==> z < x) &&
   (forall z :: z in tset(r) ==> x < z)
}

/* Check if t is a Binary Search Tree */
predicate BST(t: LLRB)
{
    match t
        case Empty            => true
        case Node(l, _, x, r) => BST_Root(l, x, r) &&
                                 BST(l) &&
                                 BST(r)
}

predicate balanced(t: LLRB)
{
    match t
        case Empty            => true
        case Node(l, _, x, r) => bHeight(l) == bHeight(r)
}

/* Check color constriants of LLRB, i.e. a red node's children must be black and t must be left-leaning */
predicate goodColor(t: LLRB)
{
    match t
        case Empty            => true
        case Node(l, c, _, r) => 
            match c
                case Red   => color(l) == Black && color(r) == Black			
                case Black => color(r) == Red ==> color(l) == Red
}

/* Requires the root color to be black and an isolated red child. This is a temporary state in deletion.*/
predicate mirrorLLRB (t: LLRB)
{
    match t
        case Empty            => true
        case Node(l, c, k, r) => isLLRB(l) &&
                                 isLLRB(r) &&
                                 balanced(t) &&
                                 BST(t) &&
                                 c == Black && color(r) == Red && color(l) == Black
}

predicate notEmpty(t: LLRB)
{
    t.Node?
}

predicate empty(t: LLRB)
{
    t.Empty?
}
