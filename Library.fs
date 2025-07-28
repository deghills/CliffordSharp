namespace Clifford

#nowarn 3535
open System

[<AutoOpen>]
module private ByteExtensions =
    type Byte with 
        member this.Item b = 1uy = ((this >>> b) &&& 1uy)
        member this.toBitVectorString = String [|  
            'e'
            for i in 0..7 do
                if this[i] then
                    yield! (i + 1).ToString()
        |]

    let buildRepunit n =
        let rec aux acc = function
            | 1 -> (acc ||| 1uy)
            | i ->
                let ndecr = i - 1
                aux (acc ||| (1uy <<< ndecr)) ndecr
        in aux n

    let indeces (bld: byte) =
        [ for i in 0..7 do
            if bld[i] then yield i ]

module Clifford =
    type ICliffordSignature =
        static abstract member P : int
        static abstract member Q : int
        static abstract member N : int

    [<RequireQualifiedAccess>]
    module Signature =
        let size<'signature when 'signature :> ICliffordSignature> =
            'signature.P + 'signature.Q + 'signature.N

        let toString<'signature when 'signature :> ICliffordSignature> =
            $"P: {'signature.P}, Q: {'signature.Q}, N: {'signature.N}"

        let basis<'signature when 'signature :> ICliffordSignature> =
            [| for i in 1..size<'signature> ->
                "e" + i.ToString(), 1uy <<< (i - 1) |]
            // would be nice to have this make basis n-vectors for all grades, instead of just 1-vectors

    [<RequireQualifiedAccess>]
    module Blade =
        let zero = 0uy, 0f

        let potency<'signature when 'signature :> ICliffordSignature> (bld: byte) =
            let rec aux sgn = function
                | i when bld[i] && i >= Signature.size<'signature> ->
                    failwith "this blade is not valid in this signature"
                
                | i when i < 0 ->
                    sgn
                
                | i when bld[i] && 'signature.P <= i && i < 'signature.P + 'signature.Q ->
                    aux (sgn * -1f) (i - 1)
                
                | i when bld[i] && i >= 'signature.P + 'signature.Q ->
                    aux 0f (i - 1)
                
                | i ->
                    aux sgn (i - 1)
            in aux 1f 7

        let signFromSquares<'signature when 'signature :> ICliffordSignature> a b =
            potency<'signature> (a &&& b)

        let signFromSwaps a b =
            //single mergesort iteration
            let rec inversionCounter lhs rhs acc =
                match lhs, rhs with
                | [], _ | _, [] -> 
                    acc

                | x :: xs, y :: ys when (x > y) -> 
                    inversionCounter (x :: xs) ys (acc + xs.Length + 1)

                | _ :: xs, y :: ys -> 
                    inversionCounter xs (y :: ys) acc
            in
            match (inversionCounter (indeces a) (indeces b) 0) % 2 with
            | 0 -> 1f
            | _ -> -1f

        let sgn<'signature when 'signature :> ICliffordSignature> a b = (signFromSquares<'signature> a b) * (signFromSwaps a b)

        let grade : byte -> int =
            uint32 >> System.Numerics.BitOperations.PopCount

        let dual<'signature when 'signature :> ICliffordSignature> (bld, mag) =
            let bld' = (buildRepunit 0uy Signature.size<'signature>) ^^^ bld in
            let sign = signFromSwaps bld bld' in
            bld', sign * mag

        let dualInv<'signature when 'signature :> ICliffordSignature> (bld, mag) =
            let bld' = (buildRepunit 0uy Signature.size<'signature>) ^^^ bld in
            let sign = signFromSwaps bld' bld in
            bld', sign * mag

        let product<'signature when 'signature :> ICliffordSignature> (bld1, mag1) (bld2, mag2) =
            bld1 ^^^ bld2, mag1 * mag2 * (sgn<'signature> bld1 bld2)

        let wedge<'signature when 'signature :> ICliffordSignature> (bld1, mag1) (bld2, mag2) =
            let areOrthogonal a b = a &&& b = 0uy in
            if areOrthogonal bld1 bld2 then
                product<'signature> (bld1, mag1) (bld2, mag2)
            else
                zero

        let dot<'signature when 'signature :> ICliffordSignature> (bld1, mag1) (bld2, mag2) =
            let areParallel a b =
                let aOrB = a ||| b
                aOrB = a (*left contraction*) || aOrB = b (*right contraction*)
            in
            if areParallel bld1 bld2 then
                product<'signature> (bld1, mag1) (bld2, mag2)
            else
                zero

        let bilinearCombination f a b =
            Seq.collect (function 
                KeyValue bld1 ->
                    Seq.map (function 
                        KeyValue bld2 ->
                            f bld1 bld2)
                        b)
                a

    type Multivector<'signature when 'signature :> ICliffordSignature> private (sortedBlades: Map<byte, float32>) =
        new (blades: seq<byte*float32>) =
            let (|ValidBlade|_|) = function
                | 0uy, mag ->
                    Some (0uy, mag)
                
                | bld, mag when Numerics.BitOperations.Log2 (uint32 bld) < Signature.size<'signature> ->
                    Some (bld, mag)
                
                | _ ->
                    None
            in Multivector 
                (blades 
                |> Seq.fold
                    (fun acc -> function
                        | ValidBlade (nextBld, nextMag) ->
                            Map.change
                                nextBld
                                (function None -> Some nextMag | Some lastMag -> Some (lastMag + nextMag))
                                acc
                        | _ ->
                            failwith $"this blade is not valid for a clifford algebra of size: {Signature.size<'signature>}")
                    Map.empty 
                |> Map.filter (fun _ mag -> MathF.Abs mag > Single.MinValue))

        member _.ToMap = sortedBlades
        member _.ToSeq = Map.toSeq sortedBlades
        member _.ToArray = Map.toArray sortedBlades
        member _.ToList = Map.toList sortedBlades

        member _.Item b = match sortedBlades.TryFind b with Some mag -> mag | None -> 0f

        member _.Grade =
            Map.fold
                (fun acc bld _ -> Set.add (Blade.grade bld) acc)
                Set.empty
                sortedBlades

        member _.Reverse =
            Map.map
                (fun bld mag ->
                    match Blade.grade bld with
                    |2 |3 |6| 7 -> -mag
                    |_ -> mag)
                sortedBlades
            |> Multivector<'signature>

        member _.Dual =
            Seq.map
                (function KeyValue(bld, mag) -> Blade.dual<'signature> (bld, mag))
                sortedBlades
            |> Multivector<'signature>

        member _.DualInv =
            Seq.map
                (function KeyValue(bld, mag) -> Blade.dualInv<'signature> (bld, mag))
                sortedBlades
            |> Multivector<'signature>

        static member Zero = Multivector<'signature> Map.empty

        static member (~+) (m: Multivector<'signature>) = m

        static member (~-) (m: Multivector<'signature>) =
            Multivector
                (Map.map 
                    (fun _ mag -> -mag) 
                    m.ToMap)

        static member (+) (lhs: Multivector<'signature>, rhs: Multivector<'signature>) =
            Map.fold
                (fun acc bld magRight ->
                    Map.change
                        bld
                        (function None -> Some magRight | Some magLeft -> Some (magLeft + magRight))
                        acc
                )
                lhs.ToMap
                rhs.ToMap
            |> Map.filter (fun _ mag -> MathF.Abs mag > Single.Epsilon)
            |> Multivector<'signature>

        static member (-) (lhs: Multivector<'signature>, rhs: Multivector<'signature>) =
            Map.fold
                (fun acc bld magRight ->
                    Map.change
                        bld
                        (function 
                            | None -> Some -magRight 
                            | Some magLeft -> Some (magLeft - magRight)
                        )
                        acc
                )
                lhs.ToMap
                rhs.ToMap
            |> Map.filter (fun _ mag -> MathF.Abs mag > Single.Epsilon)
            |> Multivector<'signature>

        ///Geometric/Clifford product
        static member (*) (lhs: Multivector<'signature>, rhs: Multivector<'signature>) =
            Blade.bilinearCombination
                Blade.product<'signature>
                lhs.ToMap
                rhs.ToMap
            |> Multivector<'signature>

        ///Dot/Inner product
        static member (.*) (lhs: Multivector<'signature>, rhs: Multivector<'signature>) =
            Blade.bilinearCombination 
                Blade.dot<'signature>
                lhs.ToMap
                rhs.ToMap
            |> Multivector<'signature>

        ///Wedge/Outer/Exterior/Grassman product
        static member (^*) (lhs: Multivector<'signature>, rhs: Multivector<'signature>) =
            Blade.bilinearCombination 
                Blade.wedge<'signature>
                lhs.ToMap
                rhs.ToMap
            |> Multivector<'signature>

        ///Regressive product
        static member (!*) (lhs: Multivector<'signature>, rhs: Multivector<'signature>) =
            (lhs.Dual ^* rhs.Dual).DualInv

        ///Grade Projection
        static member (>.) (m: Multivector<'signature>, grade: int Set) =
            Map.filter
                (fun bld _ -> grade.Contains (Blade.grade bld))
                m.ToMap
            |> Multivector<'signature>

        static member (+) (scalar: float32, m: Multivector<'signature>) =
            Multivector [|0uy, scalar|] + m

        static member (+) (m: Multivector<'signature>, scalar: float32) =
            Multivector [|0uy, scalar|] + m

        static member (-) (scalar: float32, m: Multivector<'signature>) =
            Multivector [|0uy, scalar|] - m
        
        static member (-) (m: Multivector<'signature>, scalar: float32) =
            m - Multivector [|0uy, scalar|]

        static member (*) (scalar: float32, m: Multivector<'signature>) =
            Map.map
                (fun _ mag -> scalar * mag)
                m.ToMap
            |> Map.filter (fun _ mag -> MathF.Abs mag > System.Single.MinValue)
            |> Multivector<'signature>

        static member (*) (m: Multivector<'signature>, scalar: float32) =
            Map.map
                (fun _ mag -> scalar * mag)
                m.ToMap
            |> Map.filter (fun _ mag -> MathF.Abs mag > System.Single.MinValue)
            |> Multivector<'signature>

        static member (/) (m: Multivector<'signature>, scalar: float32) =
            (1f/scalar) * m

        member this.MagSqr = (this * this.Reverse).[0uy]
        member this.Mag = MathF.Sqrt this.MagSqr
        member this.Normalize =
            match this.Mag with
            | 0f -> failwith "zero divisors cannot be normalized"
            | mag -> this / mag, mag

    [<RequireQualifiedAccess>]
    module Versor =
        let inv (versor: Multivector<'signature>) = versor.Reverse / versor.MagSqr

        let sandwich (versor: Multivector<'signature>) (sandwiched: Multivector<'signature>) =
            (versor * sandwiched * inv versor)
            >. sandwiched.Grade

        let project (a: Multivector<'signature>) (b: Multivector<'signature>) =
            (a .* b) * inv b

        /// Exponentiate bivectors to get rotors
        let exp (bivector: Multivector<'signature>) =
            match sign (bivector * bivector).[0uy] with
            | -1 ->
                let bivectorHat, mag = bivector.Normalize in
                MathF.Cos mag + MathF.Sin mag * bivectorHat
            | 1 ->
                let bivectorHat, mag = bivector.Normalize in
                MathF.Cosh mag + MathF.Sinh mag * bivectorHat
            | 0 | _ ->
                1f + bivector

        /// Take the log of rotors to get their generating bivector
        let ln (rotor: Multivector<'signature>) =
            let real = rotor.[0uy]
            let bivector = rotor >. (Set.singleton 2)
            match sign (bivector * bivector).[0uy] with
            | -1 ->
                let mag = MathF.Acos real in
                let bivectorHat =
                    bivector / MathF.Sin bivector.Mag
                in mag * bivectorHat
            | 1 ->
                let mag = MathF.Acosh real in
                let bivectorHat =
                    bivector / MathF.Sinh bivector.Mag
                in mag * bivectorHat
            | 0 | _ -> 
                rotor - 1f

    [<AutoOpen>]
    module Algebras =
        type VGA2 =
            interface ICliffordSignature with
                static member P = 2
                static member Q = 0
                static member N = 0

        type VGA3 =
            interface ICliffordSignature with
                static member P = 3
                static member Q = 0
                static member N = 0

        type PGA2 =
            interface ICliffordSignature with
                static member P = 2
                static member Q = 0
                static member N = 1

        type PGA3 =
            interface ICliffordSignature with
                static member P = 3
                static member Q = 0
                static member N = 1

        type CGA2 =
            interface ICliffordSignature with
                static member P = 3
                static member Q = 1
                static member N = 0

        type CGA3 =
            interface ICliffordSignature with
                static member P = 4
                static member Q = 1
                static member N = 0