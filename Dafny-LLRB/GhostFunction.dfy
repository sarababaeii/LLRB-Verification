include "LLRB_Node.dfy"

// Black height: the maximum number of black edges from the top to the bottom
function bHeight(t: LLRB): nat
{
    match t
        case Empty            => 0
        case Node(l, c, _, r) => 
            match c
                case Black => 1 + max(bHeight(l), bHeight(r))
                case Red => max(bHeight(l), bHeight(r))
}

// Height of the tree including all colors
function height(t: LLRB): nat
{
    match t
        case Empty            => 0
        case Node(l, _, _, r) => 1 + max(height(l), height(r))
}

// The maximum of two integer numbers
function max(x: int, y: int): int
{
    if x >= y then x else y
}

// Set of all nodes
function tset(t: LLRB): set<int>
{
    match t
        case Empty            => {}
        case Node(l, _, x, r) => tset(l) + {x} + tset(r)
}

// Color of node (incoming edge). Empty nodes' colors are black
function color(t: LLRB): Color
{
    match t
        case Empty            => Black
        case Node(_, c, _, _) => c
}

// Number of nodes in the tree
function card(t: LLRB): nat
{
    match t 
        case Empty         => 0
        case Node(l,_,_,r) => 1 + card(l) + card(r)
}		

function power (n: nat) : nat
{
    if n == 0 then 1 else 2 * power(n-1)
}