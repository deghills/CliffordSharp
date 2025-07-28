open Clifford.Clifford

type M = Multivector<Algebras.PGA3>

let m =
    M
        [ 0uy, 1f
        ; 1uy, 2f
        ; 0b10uy, 3.3f ]

do printfn "%A" m