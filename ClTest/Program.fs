open Clifford

type M = Multivector<Algebras.PGA3>

let m =
    M
        [ "1", 1f
        ; "e1", 2f
        ; "e2", 3.3f ]

do printfn "%A" m