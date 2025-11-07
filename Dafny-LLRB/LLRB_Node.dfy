datatype LLRB = Empty
              | Node (left: LLRB, 
                      color: Color, 
                      key: int, 
                      right: LLRB)

datatype Color = Red 
               | Black