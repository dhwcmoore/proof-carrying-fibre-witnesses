(* Existing test-only crypto fixture, moved unchanged for harness reuse. *)
(* ---------- hex ---------- *)
let unhex s =
  let n = String.length s / 2 in
  String.init n (fun i -> Char.chr (int_of_string ("0x" ^ String.sub s (2*i) 2)))
let hex b =
  String.concat "" (List.init (String.length b)
    (fun i -> Printf.sprintf "%02x" (Char.code b.[i])))

(* ---------- SHA-256 (real) ---------- *)
let sha256_hex (b : string) : string = Sha256.to_hex (Sha256.string b)

(* ---------- Ed25519 verify (pure OCaml, RFC 8032) ---------- *)
module Ed25519 = struct
  let p = Z.(sub (pow (of_int 2) 255) (of_int 19))
  let el = Z.(add (pow (of_int 2) 252)
                  (of_string "27742317777372353535851937790883648493"))
  let d =
    Z.(erem (mul (sub p (of_int 121665)) (invert (of_int 121666) p)) p)  (* -121665/121666 *)
  let ( %! ) a b = Z.erem a b
  let modp a = a %! p
  let inv a = Z.invert a p

  let le_of_string s =
    let r = ref Z.zero in
    for i = String.length s - 1 downto 0 do
      r := Z.(add (shift_left !r 8) (of_int (Char.code s.[i])))
    done; !r

  (* recover x from y and sign bit *)
  let x_recover y sign =
    let y2 = modp Z.(mul y y) in
    let u = modp Z.(sub y2 one) in
    let v = modp Z.(add (mul d y2) one) in
    let xx = modp Z.(mul u (inv v)) in
    let exp = Z.(div (add p (of_int 3)) (of_int 8)) in
    let x = ref (Z.powm xx exp p) in
    if not (Z.equal (modp Z.(sub (mul !x !x) xx)) Z.zero) then begin
      let sq = Z.powm (Z.of_int 2) (Z.div (Z.sub p Z.one) (Z.of_int 4)) p in
      x := modp Z.(mul !x sq)
    end;
    if not (Z.equal (modp Z.(sub (mul !x !x) xx)) Z.zero) then None
    (* RFC 8032 5.1.3: if x = 0 and the sign bit is 1, decoding fails *)
    else if Z.equal !x Z.zero && sign = 1 then None
    else begin
      if Z.(equal (!x %! of_int 2) one) <> (sign = 1) then x := modp (Z.sub p !x);
      Some !x
    end

  let decompress (b : string) =
    if String.length b <> 32 then None else begin
      let n = le_of_string b in
      let sign = Z.(to_int (shift_right n 255)) in
      let y = Z.(logand n (sub (pow (of_int 2) 255) one)) in
      if Z.geq y p then None
      else match x_recover y sign with
        | None -> None
        | Some x -> Some (x, y)
      end

  (* twisted Edwards a = -1 affine addition *)
  let add (x1,y1) (x2,y2) =
    let dxy = modp Z.(mul (mul d (mul x1 x2)) (mul y1 y2)) in
    let x3 = modp Z.(mul (add (mul x1 y2) (mul y1 x2)) (inv (add one dxy))) in
    let y3 = modp Z.(mul (add (mul y1 y2) (mul x1 x2)) (inv (sub one dxy))) in
    (x3, y3)

  let scalar k pt =
    let acc = ref (Z.zero, Z.one) and base = ref pt and n = ref k in
    while Z.gt !n Z.zero do
      if Z.(equal (!n %! of_int 2) one) then acc := add !acc !base;
      base := add !base !base;
      n := Z.shift_right !n 1
    done; !acc

  let base =
    let by = modp Z.(mul (of_int 4) (inv (of_int 5))) in
    match x_recover by 0 with Some bx -> (bx, by) | None -> assert false

  let is_identity (x, y) = Z.equal x Z.zero && Z.equal y Z.one
  (* a point has order dividing the cofactor 8 iff [8]P is the identity *)
  let low_order pt = is_identity (scalar (Z.of_int 8) pt)

  (* trust-anchor key validation: 64 lowercase hex, decodes to a canonical,
     non-small-order edwards25519 point *)
  let valid_pubkey_hex (h : string) : bool =
    String.length h = 64
    && String.for_all (fun c -> (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f')) h
    && (match decompress (unhex h) with
        | Some a -> not (low_order a)
        | None -> false)

  let byte_at z i = Z.to_int (Z.logand (Z.shift_right z (8 * i)) (Z.of_int 255))

  let compress (x, y) =
    let s = Bytes.create 32 in
    for i = 0 to 31 do Bytes.set s i (Char.chr (byte_at y i)) done;
    if Z.(equal (x %! of_int 2) one) then
      Bytes.set s 31 (Char.chr (Char.code (Bytes.get s 31) lor 128));
    Bytes.to_string s

  let le_to_string n z = String.init n (fun i -> Char.chr (byte_at z i))

  let clamp32 (b : string) =
    let a = Bytes.of_string b in
    Bytes.set a 0 (Char.chr (Char.code (Bytes.get a 0) land 248));
    Bytes.set a 31 (Char.chr ((Char.code (Bytes.get a 31) land 127) lor 64));
    Bytes.to_string a

  let sign ~sk ~msg =
    let h = Sha512.to_bin (Sha512.string sk) in
    let a = le_of_string (clamp32 (String.sub h 0 32)) in
    let prefix = String.sub h 32 32 in
    let bigA = compress (scalar a base) in
    let r = Z.erem (le_of_string (Sha512.to_bin (Sha512.string (prefix ^ msg)))) el in
    let bigR = compress (scalar r base) in
    let k = Z.erem (le_of_string (Sha512.to_bin (Sha512.string (bigR ^ bigA ^ msg)))) el in
    let s = Z.erem (Z.add r (Z.mul k a)) el in
    bigR ^ le_to_string 32 s

  let pubkey ~sk =
    let h = Sha512.to_bin (Sha512.string sk) in
    compress (scalar (le_of_string (clamp32 (String.sub h 0 32))) base)

  let verify ~pub ~sig_ ~msg =
    if String.length pub <> 32 || String.length sig_ <> 64 then false
    else match decompress pub, decompress (String.sub sig_ 0 32) with
    | Some a, Some r ->
      let s = le_of_string (String.sub sig_ 32 32) in
      if Z.geq s el then false
      else begin
        let h = Sha512.to_bin (Sha512.string
                  (String.sub sig_ 0 32 ^ pub ^ msg)) in
        let k = Z.erem (le_of_string h) el in
        let lhs = scalar s base in
        let rhs = add r (scalar k a) in
        Z.equal (fst lhs) (fst rhs) && Z.equal (snd lhs) (snd rhs)
      end
    | _ -> false
end

let ed25519_verify (pub : string) (sig_ : string) (msg : string) : bool =
  Ed25519.verify ~pub ~sig_ ~msg
let ed25519_pubkey_valid (k : string) : bool = Ed25519.valid_pubkey_hex (hex k)

