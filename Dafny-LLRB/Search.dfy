include "InternalMethod.dfy"

function search(x: int, t: LLRB): (res: LLRB)
requires isLLRB(t)
ensures  isLLRB(res)
ensures  x in tset(res) ==> (notEmpty(res) && res.key == x)
ensures  empty(res) ==> x !in tset(res)
{
    match t
        case Empty            => Empty
        case Node(l, _, y, r) => if x < y
                                    then search(x, l)
                                    else if x > y
                                            then search(x, r)
                                            else t
}
