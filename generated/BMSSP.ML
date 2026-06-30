structure BMSSP : sig
  type num
  type nat
  type real
  type ('a, 'b) bucketed_partition_ext
  val example_graph : (nat * (nat * nat)) list
  val bmssp_distances : (nat * (nat * nat)) list -> nat -> (nat * nat) list
  val example_expected_dist : (nat * nat) list
end = struct

datatype num = One | Bit0 of num | Bit1 of num;

datatype int = Zero_int | Pos of num | Neg of num;

val one_inta : int = Pos One;

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_int = {one = one_inta} : int one;

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_int = {zero = Zero_int} : int zero;

type 'a zero_neq_one = {one_zero_neq_one : 'a one, zero_zero_neq_one : 'a zero};
val one_zero_neq_one = #one_zero_neq_one : 'a zero_neq_one -> 'a one;
val zero_zero_neq_one = #zero_zero_neq_one : 'a zero_neq_one -> 'a zero;

val zero_neq_one_int =
  {one_zero_neq_one = one_int, zero_zero_neq_one = zero_int} : int zero_neq_one;

datatype nat = Zero_nat | Suc of nat;

fun equal_nata Zero_nat (Suc x2) = false
  | equal_nata (Suc x2) Zero_nat = false
  | equal_nata (Suc x2) (Suc y2) = equal_nata x2 y2
  | equal_nata Zero_nat Zero_nat = true;

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_nat = {equal = equal_nata} : nat equal;

fun less_eq_nat Zero_nat n = true
  | less_eq_nat (Suc m) n = less_nat m n
and less_nat n Zero_nat = false
  | less_nat m (Suc n) = less_eq_nat m n;

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat ord;

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

type 'a order = {preorder_order : 'a preorder};
val preorder_order = #preorder_order : 'a order -> 'a preorder;

val preorder_nat = {ord_preorder = ord_nat} : nat preorder;

val order_nat = {preorder_order = preorder_nat} : nat order;

type 'a linorder = {order_linorder : 'a order};
val order_linorder = #order_linorder : 'a linorder -> 'a order;

val linorder_nat = {order_linorder = order_nat} : nat linorder;

datatype rat = Frct of (int * int);

val one_rat : rat = Frct (one_inta, one_inta);

datatype real = Ratreal of rat;

val one_reala : real = Ratreal one_rat;

val one_real = {one = one_reala} : real one;

fun plus_num One One = Bit0 One
  | plus_num One (Bit0 n) = Bit1 n
  | plus_num One (Bit1 n) = Bit0 (plus_num n One)
  | plus_num (Bit0 m) One = Bit1 m
  | plus_num (Bit0 m) (Bit0 n) = Bit0 (plus_num m n)
  | plus_num (Bit0 m) (Bit1 n) = Bit1 (plus_num m n)
  | plus_num (Bit1 m) One = Bit0 (plus_num m One)
  | plus_num (Bit1 m) (Bit0 n) = Bit1 (plus_num m n)
  | plus_num (Bit1 m) (Bit1 n) = Bit0 (plus_num (plus_num m n) One);

fun times_num m One = m
  | times_num One n = n
  | times_num (Bit0 m) (Bit0 n) = Bit0 (Bit0 (times_num m n))
  | times_num (Bit0 m) (Bit1 n) = Bit0 (times_num m (Bit1 n))
  | times_num (Bit1 m) (Bit0 n) = Bit0 (times_num (Bit1 m) n)
  | times_num (Bit1 m) (Bit1 n) =
    Bit1 (plus_num (plus_num m n) (Bit0 (times_num m n)));

fun times_int k Zero_int = Zero_int
  | times_int Zero_int l = Zero_int
  | times_int (Pos m) (Pos n) = Pos (times_num m n)
  | times_int (Pos m) (Neg n) = Neg (times_num m n)
  | times_int (Neg m) (Pos n) = Neg (times_num m n)
  | times_int (Neg m) (Neg n) = Pos (times_num m n);

fun uminus_int Zero_int = Zero_int
  | uminus_int (Pos m) = Neg m
  | uminus_int (Neg m) = Pos m;

fun bitM One = One
  | bitM (Bit0 n) = Bit1 (bitM n)
  | bitM (Bit1 n) = Bit1 (Bit0 n);

fun dup Zero_int = Zero_int
  | dup (Pos n) = Pos (Bit0 n)
  | dup (Neg n) = Neg (Bit0 n);

fun plus_int k Zero_int = k
  | plus_int Zero_int l = l
  | plus_int (Pos m) (Pos n) = Pos (plus_num m n)
  | plus_int (Pos m) (Neg n) = sub m n
  | plus_int (Neg m) (Pos n) = sub n m
  | plus_int (Neg m) (Neg n) = Neg (plus_num m n)
and sub One One = Zero_int
  | sub (Bit0 m) One = Pos (bitM m)
  | sub (Bit1 m) One = Pos (Bit0 m)
  | sub One (Bit0 n) = Neg (bitM n)
  | sub One (Bit1 n) = Neg (Bit0 n)
  | sub (Bit0 m) (Bit0 n) = dup (sub m n)
  | sub (Bit1 m) (Bit1 n) = dup (sub m n)
  | sub (Bit1 m) (Bit0 n) = plus_int (dup (sub m n)) one_inta
  | sub (Bit0 m) (Bit1 n) = minus_int (dup (sub m n)) one_inta
and minus_int k Zero_int = k
  | minus_int Zero_int l = uminus_int l
  | minus_int (Pos m) (Pos n) = sub m n
  | minus_int (Pos m) (Neg n) = Pos (plus_num m n)
  | minus_int (Neg m) (Pos n) = Neg (plus_num m n)
  | minus_int (Neg m) (Neg n) = sub n m;

fun quotient_of (Frct x) = x;

fun less_eq_num One n = true
  | less_eq_num (Bit0 m) One = false
  | less_eq_num (Bit1 m) One = false
  | less_eq_num (Bit0 m) (Bit0 n) = less_eq_num m n
  | less_eq_num (Bit0 m) (Bit1 n) = less_eq_num m n
  | less_eq_num (Bit1 m) (Bit1 n) = less_eq_num m n
  | less_eq_num (Bit1 m) (Bit0 n) = less_num m n
and less_num m One = false
  | less_num One (Bit0 n) = true
  | less_num One (Bit1 n) = true
  | less_num (Bit0 m) (Bit0 n) = less_num m n
  | less_num (Bit0 m) (Bit1 n) = less_eq_num m n
  | less_num (Bit1 m) (Bit1 n) = less_num m n
  | less_num (Bit1 m) (Bit0 n) = less_num m n;

fun less_eq_int Zero_int Zero_int = true
  | less_eq_int Zero_int (Pos l) = true
  | less_eq_int Zero_int (Neg l) = false
  | less_eq_int (Pos k) Zero_int = false
  | less_eq_int (Pos k) (Pos l) = less_eq_num k l
  | less_eq_int (Pos k) (Neg l) = false
  | less_eq_int (Neg k) Zero_int = true
  | less_eq_int (Neg k) (Pos l) = true
  | less_eq_int (Neg k) (Neg l) = less_eq_num l k;

fun less_int Zero_int Zero_int = false
  | less_int Zero_int (Pos l) = true
  | less_int Zero_int (Neg l) = false
  | less_int (Pos k) Zero_int = false
  | less_int (Pos k) (Pos l) = less_num k l
  | less_int (Pos k) (Neg l) = false
  | less_int (Neg k) Zero_int = true
  | less_int (Neg k) (Pos l) = true
  | less_int (Neg k) (Neg l) = less_num l k;

fun abs_int i = (if less_int i Zero_int then uminus_int i else i);

fun divmod_step_int l qr =
  let
    val (q, r) = qr;
  in
    (if less_eq_int (abs_int l) (abs_int r)
      then (plus_int (times_int (Pos (Bit0 One)) q) one_inta, minus_int r l)
      else (times_int (Pos (Bit0 One)) q, r))
  end;

fun divmod_int m One = (Pos m, Zero_int)
  | divmod_int One (Bit0 n) = (Zero_int, Pos One)
  | divmod_int One (Bit1 n) = (Zero_int, Pos One)
  | divmod_int (Bit0 m) (Bit0 n) = let
                                     val (q, r) = divmod_int m n;
                                   in
                                     (q, times_int (Pos (Bit0 One)) r)
                                   end
  | divmod_int (Bit1 m) (Bit0 n) =
    let
      val (q, r) = divmod_int m n;
    in
      (q, plus_int (times_int (Pos (Bit0 One)) r) one_inta)
    end
  | divmod_int (Bit0 m) (Bit1 n) =
    (if less_eq_num m n then (Zero_int, Pos (Bit0 m))
      else divmod_step_int (Pos (Bit1 n)) (divmod_int (Bit0 m) (Bit0 (Bit1 n))))
  | divmod_int (Bit1 m) (Bit1 n) =
    (if less_num m n then (Zero_int, Pos (Bit1 m))
      else divmod_step_int (Pos (Bit1 n))
             (divmod_int (Bit1 m) (Bit0 (Bit1 n))));

fun fst (x1, x2) = x1;

fun of_bool A_ false = zero (zero_zero_neq_one A_)
  | of_bool A_ true = one (one_zero_neq_one A_);

fun equal_num (Bit0 x2) (Bit1 x3) = false
  | equal_num (Bit1 x3) (Bit0 x2) = false
  | equal_num One (Bit1 x3) = false
  | equal_num (Bit1 x3) One = false
  | equal_num One (Bit0 x2) = false
  | equal_num (Bit0 x2) One = false
  | equal_num (Bit1 x3) (Bit1 y3) = equal_num x3 y3
  | equal_num (Bit0 x2) (Bit0 y2) = equal_num x2 y2
  | equal_num One One = true;

fun equal_int Zero_int Zero_int = true
  | equal_int Zero_int (Pos l) = false
  | equal_int Zero_int (Neg l) = false
  | equal_int (Pos k) Zero_int = false
  | equal_int (Pos k) (Pos l) = equal_num k l
  | equal_int (Pos k) (Neg l) = false
  | equal_int (Neg k) Zero_int = false
  | equal_int (Neg k) (Pos l) = false
  | equal_int (Neg k) (Neg l) = equal_num k l;

fun adjust_div (q, r) =
  plus_int q (of_bool zero_neq_one_int (not (equal_int r Zero_int)));

fun divide_int k Zero_int = Zero_int
  | divide_int Zero_int k = Zero_int
  | divide_int k (Pos One) = k
  | divide_int k (Neg One) = uminus_int k
  | divide_int (Pos m) (Pos n) = fst (divmod_int m n)
  | divide_int (Neg m) (Pos n) = uminus_int (adjust_div (divmod_int m n))
  | divide_int (Pos m) (Neg n) = uminus_int (adjust_div (divmod_int m n))
  | divide_int (Neg m) (Neg n) = fst (divmod_int m n);

fun snd (x1, x2) = x2;

fun adjust_mod l r =
  (if equal_int r Zero_int then Zero_int else minus_int (Pos l) r);

fun modulo_int k Zero_int = k
  | modulo_int Zero_int k = Zero_int
  | modulo_int k (Pos One) = Zero_int
  | modulo_int k (Neg One) = Zero_int
  | modulo_int (Pos m) (Pos n) = snd (divmod_int m n)
  | modulo_int (Neg m) (Pos n) = adjust_mod n (snd (divmod_int m n))
  | modulo_int (Pos m) (Neg n) =
    uminus_int (adjust_mod n (snd (divmod_int m n)))
  | modulo_int (Neg m) (Neg n) = uminus_int (snd (divmod_int m n));

fun gcd_int k l =
  abs_int
    (if equal_int l Zero_int then k
      else gcd_int l (modulo_int (abs_int k) (abs_int l)));

fun normalize p =
  (if less_int Zero_int (snd p)
    then let
           val a = gcd_int (fst p) (snd p);
         in
           (divide_int (fst p) a, divide_int (snd p) a)
         end
    else (if equal_int (snd p) Zero_int then (Zero_int, one_inta)
           else let
                  val a = uminus_int (gcd_int (fst p) (snd p));
                in
                  (divide_int (fst p) a, divide_int (snd p) a)
                end));

fun plus_rat p q =
  Frct let
         val (a, c) = quotient_of p;
         val (b, d) = quotient_of q;
       in
         normalize (plus_int (times_int a d) (times_int b c), times_int c d)
       end;

fun plus_reala (Ratreal x) (Ratreal y) = Ratreal (plus_rat x y);

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

val plus_real = {plus = plus_reala} : real plus;

val zero_rat : rat = Frct (Zero_int, one_inta);

val zero_reala : real = Ratreal zero_rat;

val zero_real = {zero = zero_reala} : real zero;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};
val plus_semigroup_add = #plus_semigroup_add : 'a semigroup_add -> 'a plus;

type 'a numeral =
  {one_numeral : 'a one, semigroup_add_numeral : 'a semigroup_add};
val one_numeral = #one_numeral : 'a numeral -> 'a one;
val semigroup_add_numeral = #semigroup_add_numeral :
  'a numeral -> 'a semigroup_add;

val semigroup_add_real = {plus_semigroup_add = plus_real} : real semigroup_add;

val numeral_real =
  {one_numeral = one_real, semigroup_add_numeral = semigroup_add_real} :
  real numeral;

fun times_rat p q = Frct let
                           val (a, c) = quotient_of p;
                           val (b, d) = quotient_of q;
                         in
                           normalize (times_int a b, times_int c d)
                         end;

fun times_reala (Ratreal x) (Ratreal y) = Ratreal (times_rat x y);

type 'a times = {times : 'a -> 'a -> 'a};
val times = #times : 'a times -> 'a -> 'a -> 'a;

type 'a power = {one_power : 'a one, times_power : 'a times};
val one_power = #one_power : 'a power -> 'a one;
val times_power = #times_power : 'a power -> 'a times;

val times_real = {times = times_reala} : real times;

val power_real = {one_power = one_real, times_power = times_real} : real power;

fun less_eq_rat p q = let
                        val (a, c) = quotient_of p;
                        val (b, d) = quotient_of q;
                      in
                        less_eq_int (times_int a d) (times_int c b)
                      end;

fun less_eq_real (Ratreal x) (Ratreal y) = less_eq_rat x y;

fun less_rat p q = let
                     val (a, c) = quotient_of p;
                     val (b, d) = quotient_of q;
                   in
                     less_int (times_int a d) (times_int c b)
                   end;

fun less_real (Ratreal x) (Ratreal y) = less_rat x y;

val ord_real = {less_eq = less_eq_real, less = less_real} : real ord;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};
val semigroup_add_ab_semigroup_add = #semigroup_add_ab_semigroup_add :
  'a ab_semigroup_add -> 'a semigroup_add;

type 'a semigroup_mult = {times_semigroup_mult : 'a times};
val times_semigroup_mult = #times_semigroup_mult :
  'a semigroup_mult -> 'a times;

type 'a semiring =
  {ab_semigroup_add_semiring : 'a ab_semigroup_add,
    semigroup_mult_semiring : 'a semigroup_mult};
val ab_semigroup_add_semiring = #ab_semigroup_add_semiring :
  'a semiring -> 'a ab_semigroup_add;
val semigroup_mult_semiring = #semigroup_mult_semiring :
  'a semiring -> 'a semigroup_mult;

val ab_semigroup_add_real =
  {semigroup_add_ab_semigroup_add = semigroup_add_real} : real ab_semigroup_add;

val semigroup_mult_real = {times_semigroup_mult = times_real} :
  real semigroup_mult;

val semiring_real =
  {ab_semigroup_add_semiring = ab_semigroup_add_real,
    semigroup_mult_semiring = semigroup_mult_real}
  : real semiring;

val preorder_real = {ord_preorder = ord_real} : real preorder;

val order_real = {preorder_order = preorder_real} : real order;

type 'a mult_zero = {times_mult_zero : 'a times, zero_mult_zero : 'a zero};
val times_mult_zero = #times_mult_zero : 'a mult_zero -> 'a times;
val zero_mult_zero = #zero_mult_zero : 'a mult_zero -> 'a zero;

val mult_zero_real = {times_mult_zero = times_real, zero_mult_zero = zero_real}
  : real mult_zero;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add, zero_monoid_add : 'a zero};
val semigroup_add_monoid_add = #semigroup_add_monoid_add :
  'a monoid_add -> 'a semigroup_add;
val zero_monoid_add = #zero_monoid_add : 'a monoid_add -> 'a zero;

type 'a comm_monoid_add =
  {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add,
    monoid_add_comm_monoid_add : 'a monoid_add};
val ab_semigroup_add_comm_monoid_add = #ab_semigroup_add_comm_monoid_add :
  'a comm_monoid_add -> 'a ab_semigroup_add;
val monoid_add_comm_monoid_add = #monoid_add_comm_monoid_add :
  'a comm_monoid_add -> 'a monoid_add;

type 'a semiring_0 =
  {comm_monoid_add_semiring_0 : 'a comm_monoid_add,
    mult_zero_semiring_0 : 'a mult_zero, semiring_semiring_0 : 'a semiring};
val comm_monoid_add_semiring_0 = #comm_monoid_add_semiring_0 :
  'a semiring_0 -> 'a comm_monoid_add;
val mult_zero_semiring_0 = #mult_zero_semiring_0 :
  'a semiring_0 -> 'a mult_zero;
val semiring_semiring_0 = #semiring_semiring_0 : 'a semiring_0 -> 'a semiring;

val monoid_add_real =
  {semigroup_add_monoid_add = semigroup_add_real, zero_monoid_add = zero_real} :
  real monoid_add;

val comm_monoid_add_real =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_real,
    monoid_add_comm_monoid_add = monoid_add_real}
  : real comm_monoid_add;

val semiring_0_real =
  {comm_monoid_add_semiring_0 = comm_monoid_add_real,
    mult_zero_semiring_0 = mult_zero_real, semiring_semiring_0 = semiring_real}
  : real semiring_0;

type 'a monoid_mult =
  {semigroup_mult_monoid_mult : 'a semigroup_mult,
    power_monoid_mult : 'a power};
val semigroup_mult_monoid_mult = #semigroup_mult_monoid_mult :
  'a monoid_mult -> 'a semigroup_mult;
val power_monoid_mult = #power_monoid_mult : 'a monoid_mult -> 'a power;

type 'a semiring_numeral =
  {monoid_mult_semiring_numeral : 'a monoid_mult,
    numeral_semiring_numeral : 'a numeral,
    semiring_semiring_numeral : 'a semiring};
val monoid_mult_semiring_numeral = #monoid_mult_semiring_numeral :
  'a semiring_numeral -> 'a monoid_mult;
val numeral_semiring_numeral = #numeral_semiring_numeral :
  'a semiring_numeral -> 'a numeral;
val semiring_semiring_numeral = #semiring_semiring_numeral :
  'a semiring_numeral -> 'a semiring;

type 'a semiring_1 =
  {semiring_numeral_semiring_1 : 'a semiring_numeral,
    semiring_0_semiring_1 : 'a semiring_0,
    zero_neq_one_semiring_1 : 'a zero_neq_one};
val semiring_numeral_semiring_1 = #semiring_numeral_semiring_1 :
  'a semiring_1 -> 'a semiring_numeral;
val semiring_0_semiring_1 = #semiring_0_semiring_1 :
  'a semiring_1 -> 'a semiring_0;
val zero_neq_one_semiring_1 = #zero_neq_one_semiring_1 :
  'a semiring_1 -> 'a zero_neq_one;

val monoid_mult_real =
  {semigroup_mult_monoid_mult = semigroup_mult_real,
    power_monoid_mult = power_real}
  : real monoid_mult;

val semiring_numeral_real =
  {monoid_mult_semiring_numeral = monoid_mult_real,
    numeral_semiring_numeral = numeral_real,
    semiring_semiring_numeral = semiring_real}
  : real semiring_numeral;

val zero_neq_one_real =
  {one_zero_neq_one = one_real, zero_zero_neq_one = zero_real} :
  real zero_neq_one;

val semiring_1_real =
  {semiring_numeral_semiring_1 = semiring_numeral_real,
    semiring_0_semiring_1 = semiring_0_real,
    zero_neq_one_semiring_1 = zero_neq_one_real}
  : real semiring_1;

val linorder_real = {order_linorder = order_real} : real linorder;

datatype 'a set = Set of 'a list | Coset of 'a list;

datatype ('a, 'b) bp_bucket_ext = Bp_bucket_ext of real * ('a * real) list * 'b;

datatype ('a, 'b) bucketed_partition_ext =
  Bucketed_partition_ext of
    nat * real * ('a, unit) bp_bucket_ext list * ('a -> real) * 'b;

fun id x = (fn xa => xa) x;

fun eq A_ a b = equal A_ a b;

fun drop n [] = []
  | drop n (x :: xs) = (case n of Zero_nat => x :: xs | Suc m => drop m xs);

fun maps f [] = []
  | maps f (x :: xs) = f x @ maps f xs;

fun null [] = true
  | null (x :: xs) = false;

fun take n [] = []
  | take n (x :: xs) = (case n of Zero_nat => [] | Suc m => x :: take m xs);

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun image f (Set xs) = Set (map f xs);

fun foldr f [] = id
  | foldr f (x :: xs) = f x o foldr f xs;

fun membera A_ [] y = false
  | membera A_ (x :: xs) y = eq A_ x y orelse membera A_ xs y;

fun member A_ x (Set xs) = membera A_ xs x
  | member A_ x (Coset xs) = not (membera A_ xs x);

fun fun_upd A_ f a b = (fn x => (if eq A_ x a then b else f x));

fun filter p [] = []
  | filter p (x :: xs) = (if p x then x :: filter p xs else filter p xs);

fun hd (x21 :: x22) = x21;

fun remdups A_ [] = []
  | remdups A_ (x :: xs) =
    (if membera A_ xs x then remdups A_ xs else x :: remdups A_ xs);

fun plus_nat Zero_nat n = n
  | plus_nat (Suc m) n = plus_nat m (Suc n);

val one_nat : nat = Suc Zero_nat;

fun nat_of_num One = one_nat
  | nat_of_num (Bit0 n) = let
                            val m = nat_of_num n;
                          in
                            plus_nat m m
                          end
  | nat_of_num (Bit1 n) = let
                            val m = nat_of_num n;
                          in
                            Suc (plus_nat m m)
                          end;

fun list_all p [] = true
  | list_all p (x :: xs) = p x andalso list_all p xs;

fun length_tailrec [] n = n
  | length_tailrec (x :: xs) n = length_tailrec xs (Suc n);

fun max A_ a b = (if less_eq A_ a b then b else a);

fun min A_ a b = (if less_eq A_ a b then a else b);

val bot_set : 'a set = Set [];

fun minus_nat m Zero_nat = m
  | minus_nat Zero_nat n = Zero_nat
  | minus_nat (Suc m) (Suc n) = minus_nat m n;

fun divmod_nat m n =
  (if equal_nata n Zero_nat orelse less_nat m n then (Zero_nat, m)
    else let
           val (q, a) = divmod_nat (minus_nat m n) n;
         in
           (Suc q, a)
         end);

fun of_nat_aux A_ inc Zero_nat i = i
  | of_nat_aux A_ inc (Suc n) i = of_nat_aux A_ inc n (inc i);

fun of_nat A_ n =
  of_nat_aux A_
    (fn i =>
      plus ((plus_semigroup_add o semigroup_add_numeral o
              numeral_semiring_numeral o semiring_numeral_semiring_1)
             A_)
        i (one ((one_numeral o numeral_semiring_numeral o
                  semiring_numeral_semiring_1)
                 A_)))
    n (zero ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1)
              A_));

fun bp_buckets
  (Bucketed_partition_ext
    (bp_block_size, bp_upper_bound, bp_buckets, bp_values, more))
  = bp_buckets;

fun bp_bucket_entries (Bp_bucket_ext (bp_marker, bp_bucket_entries, more)) =
  bp_bucket_entries;

fun bp_bucket_entries_flat bs = maps bp_bucket_entries bs;

fun bp_bucket_below_bound b beta =
  list_all (fn p => less_real (snd p) beta) (bp_bucket_entries b);

fun bp_marker (Bp_bucket_ext (bp_marker, bp_bucket_entries, more)) = bp_marker;

fun bp_entries p = bp_bucket_entries_flat (bp_buckets p);

fun size_list xs = length_tailrec xs Zero_nat;

fun bp_can_first_bucket_pull m p =
  (case bp_buckets p of [] => false | [_] => false
    | b :: c :: bs =>
      less_nat m (size_list (bp_entries p)) andalso
        (less_eq_nat (size_list (bp_bucket_entries b)) m andalso
          (bp_bucket_below_bound b (bp_marker c) andalso
            not (null (bp_bucket_entries_flat (c :: bs))))));

fun bp_buckets_update bp_bucketsa
  (Bucketed_partition_ext
    (bp_block_size, bp_upper_bound, bp_buckets, bp_values, more))
  = Bucketed_partition_ext
      (bp_block_size, bp_upper_bound, bp_bucketsa bp_buckets, bp_values, more);

fun bp_bucket_entries_update bp_bucket_entriesa
  (Bp_bucket_ext (bp_marker, bp_bucket_entries, more)) =
  Bp_bucket_ext (bp_marker, bp_bucket_entriesa bp_bucket_entries, more);

fun bp_delete_keys_from_bucket A_ s b =
  bp_bucket_entries_update
    (fn _ => filter (fn p => not (member A_ (fst p) s)) (bp_bucket_entries b))
    b;

fun bp_delete_keys A_ s p =
  bp_buckets_update
    (fn _ => map (bp_delete_keys_from_bucket A_ s) (bp_buckets p)) p;

fun bp_entry_keys xs = image fst (Set xs);

fun bp_bucket_keys b = bp_entry_keys (bp_bucket_entries b);

fun bp_first_bucket_pull A_ m b p =
  (case bp_buckets p of [] => (bot_set, (b, p)) | [_] => (bot_set, (b, p))
    | ba :: c :: _ => let
                        val s = bp_bucket_keys ba;
                      in
                        (s, (bp_marker c, bp_delete_keys A_ s p))
                      end);

fun bp_min_value b [] = b
  | bp_min_value ba ((x, b) :: xs) = min ord_real b (bp_min_value ba xs);

fun bp_pull_bound m b p =
  (if less_eq_nat (size_list (bp_entries p)) m then b
    else bp_min_value b (bp_entries p));

fun bp_pull_set m p =
  (if less_eq_nat (size_list (bp_entries p)) m then bp_entry_keys (bp_entries p)
    else bot_set);

fun bp_conservative_pull A_ m b p = let
                                      val s = bp_pull_set m p;
                                      val beta = bp_pull_bound m b p;
                                    in
                                      (s, (beta, bp_delete_keys A_ s p))
                                    end;

fun bp_pull A_ m b p =
  (if bp_can_first_bucket_pull m p then bp_first_bucket_pull A_ m b p
    else bp_conservative_pull A_ m b p);

fun divide_rat p q = Frct let
                            val (a, c) = quotient_of p;
                            val (b, d) = quotient_of q;
                          in
                            normalize (times_int a d, times_int c b)
                          end;

fun divide_real (Ratreal x) (Ratreal y) = Ratreal (divide_rat x y);

fun bmssp_partition_key x d =
  plus_reala (of_nat semiring_1_real d)
    (divide_real (of_nat semiring_1_real x) (of_nat semiring_1_real (Suc x)));

fun bmssp_lookup_dist [] x = NONE
  | bmssp_lookup_dist ((y, d) :: ds) x =
    (if equal_nata x y then SOME d else bmssp_lookup_dist ds x);

fun bmssp_set_dist x d [] = [(x, d)]
  | bmssp_set_dist x d ((y, e) :: ds) =
    (if equal_nata x y then (x, d) :: ds else (y, e) :: bmssp_set_dist x d ds);

fun bmssp_relax_edges [] settled u du ds = ([], ds)
  | bmssp_relax_edges ((a, (b, w)) :: es) settled u du ds =
    let
      val (updates, ds1) = bmssp_relax_edges es settled u du ds;
    in
      (if equal_nata a u andalso not (membera equal_nat settled b)
        then let
               val nd = plus_nat du w;
             in
               (case bmssp_lookup_dist ds1 b
                 of NONE =>
                   ((b, bmssp_partition_key b nd) :: updates,
                     bmssp_set_dist b nd ds1)
                 | SOME old =>
                   (if less_nat nd old
                     then ((b, bmssp_partition_key b nd) :: updates,
                            bmssp_set_dist b nd ds1)
                     else (updates, ds1)))
             end
        else (updates, ds1))
    end;

fun bmssp_relax_vertices g settled [] ds = ([], ds)
  | bmssp_relax_vertices g settled (u :: us) ds =
    (case bmssp_lookup_dist ds u of NONE => bmssp_relax_vertices g settled us ds
      | SOME du =>
        let
          val (updates_u, ds1) = bmssp_relax_edges g settled u du ds;
          val (updates_us, a) = bmssp_relax_vertices g settled us ds1;
        in
          (updates_u @ updates_us, a)
        end);

fun insort_key B_ f x [] = [x]
  | insort_key B_ f x (y :: ys) =
    (if less_eq ((ord_preorder o preorder_order o order_linorder) B_) (f x)
          (f y)
      then x :: y :: ys else y :: insort_key B_ f x ys);

fun sort_key B_ f xs = foldr (insort_key B_ f) xs [];

fun bmssp_normalize_dist ds = sort_key linorder_nat fst ds;

fun bp_block_size
  (Bucketed_partition_ext
    (bp_block_size, bp_upper_bound, bp_buckets, bp_values, more))
  = bp_block_size;

fun bp_values_update bp_valuesa
  (Bucketed_partition_ext
    (bp_block_size, bp_upper_bound, bp_buckets, bp_values, more))
  = Bucketed_partition_ext
      (bp_block_size, bp_upper_bound, bp_buckets, bp_valuesa bp_values, more);

fun bp_marker_update bp_markera
  (Bp_bucket_ext (bp_marker, bp_bucket_entries, more)) =
  Bp_bucket_ext (bp_markera bp_marker, bp_bucket_entries, more);

fun bp_rebase_first_bucket_marker beta [] = []
  | bp_rebase_first_bucket_marker beta (b :: bs) =
    bp_marker_update (fn _ => beta) b :: bs;

fun bp_values
  (Bucketed_partition_ext
    (bp_block_size, bp_upper_bound, bp_buckets, bp_values, more))
  = bp_values;

fun bp_batch_value_update A_ [] f = f
  | bp_batch_value_update A_ ((x, b) :: xs) f =
    bp_batch_value_update A_ xs (fun_upd A_ f x b);

fun bp_drop_empty_prefix [] = []
  | bp_drop_empty_prefix (b :: bs) =
    (if null (bp_bucket_entries b) then bp_drop_empty_prefix bs else b :: bs);

fun bp_make_bucket xs = Bp_bucket_ext (snd (hd xs), xs, ());

fun bp_bucketize_sorted_entries_aux Zero_nat m xs = []
  | bp_bucketize_sorted_entries_aux (Suc fuel) m xs =
    (if equal_nata m Zero_nat orelse null xs then []
      else bp_make_bucket (take m xs) ::
             bp_bucketize_sorted_entries_aux fuel m (drop m xs));

fun bp_bucketize_sorted_entries m xs =
  bp_bucketize_sorted_entries_aux (size_list xs) m xs;

fun bp_bucketize_entries m xs =
  bp_bucketize_sorted_entries m (sort_key linorder_real snd xs);

fun bp_batch_max_value beta [] = beta
  | bp_batch_max_value beta ((x, b) :: xs) =
    bp_batch_max_value (max ord_real beta b) xs;

fun bp_bucketed_batch_prepend_state A_ xs p =
  (case xs of [] => p
    | pa :: ps =>
      let
        val beta = bp_batch_max_value (snd pa) ps;
        val new = bp_bucketize_entries (bp_block_size p) xs;
        val old =
          bp_rebase_first_bucket_marker beta
            (bp_drop_empty_prefix (bp_buckets p));
      in
        bp_values_update (fn _ => bp_batch_value_update A_ xs (bp_values p))
          (bp_buckets_update (fn _ => new @ old) p)
      end);

fun divide_nat m n = fst (divmod_nat m n);

fun floor_log n =
  (if less_nat n (nat_of_num (Bit0 One)) then Zero_nat
    else Suc (floor_log (divide_nat n (nat_of_num (Bit0 One)))));

fun bp_ratio_log_budget n m = Suc (floor_log (Suc (divide_nat n m)));

fun times_nat Zero_nat n = Zero_nat
  | times_nat (Suc m) n = plus_nat n (times_nat m n);

fun bp_batch_prepend_log_budget xs m =
  times_nat (size_list xs) (bp_ratio_log_budget (size_list xs) m);

fun c_bp_bucketed_batch_prepend_direct_actual A_ xs p =
  (bp_bucketed_batch_prepend_state A_ xs p,
    bp_batch_prepend_log_budget xs (bp_block_size p));

fun c_bp_paper_batch_prepend A_ xs p =
  c_bp_bucketed_batch_prepend_direct_actual A_ xs p;

fun bp_result_of r = fst r;

fun bmssp_trim_empty_prefix p =
  bp_buckets_update (fn _ => bp_drop_empty_prefix (bp_buckets p)) p;

fun bp_bucket_search_steps p = Suc (floor_log (size_list (bp_buckets p)));

fun bp_local_insert_search_charge p = Suc (bp_bucket_search_steps p);

fun bp_local_insert_bucket m p [] = bp_bucketize_entries m [p]
  | bp_local_insert_bucket m p [b] =
    (if less_real (snd p) (bp_marker b) then bp_bucketize_entries m [p] @ [b]
      else bp_bucketize_entries m (p :: bp_bucket_entries b))
  | bp_local_insert_bucket m p (b :: c :: bs) =
    (if less_real (snd p) (bp_marker b)
      then bp_bucketize_entries m [p] @ b :: c :: bs
      else (if less_real (snd p) (bp_marker c)
             then bp_bucketize_entries m (p :: bp_bucket_entries b) @ c :: bs
             else b :: bp_local_insert_bucket m p (c :: bs)));

fun bp_delete_key_from_bucket A_ x b =
  bp_bucket_entries_update
    (fn _ => filter (fn p => not (eq A_ (fst p) x)) (bp_bucket_entries b)) b;

fun bp_delete_key A_ x p =
  bp_buckets_update
    (fn _ => map (bp_delete_key_from_bucket A_ x) (bp_buckets p)) p;

fun bp_local_insert_state A_ x b p =
  let
    val ba =
      (if member A_ x (bp_entry_keys (bp_entries p))
        then min ord_real (bp_values p x) b else b);
    val p0 = bp_delete_key A_ x p;
  in
    bp_values_update (fn _ => fun_upd A_ (bp_values p) x ba)
      (bp_buckets_update
        (fn _ =>
          bp_local_insert_bucket (bp_block_size p0) (x, ba) (bp_buckets p0))
        p0)
  end;

fun bp_rebucket p =
  bp_buckets_update
    (fn _ => bp_bucketize_entries (bp_block_size p) (bp_entries p)) p;

fun bp_regularized_local_insert A_ x b p =
  bp_rebucket (bp_local_insert_state A_ x b p);

fun c_bp_regularized_local_insert A_ x b p =
  (bp_regularized_local_insert A_ x b p, bp_local_insert_search_charge p);

fun bmssp_insert_updates [] p = p
  | bmssp_insert_updates ((x, b) :: xs) p =
    bmssp_insert_updates xs
      (bp_result_of (c_bp_regularized_local_insert equal_nat x b p));

fun bmssp_apply_updates xs p =
  let
    val p0 = bmssp_trim_empty_prefix p;
  in
    (if null (bp_entries p0)
      then bp_result_of (c_bp_paper_batch_prepend equal_nat xs p0)
      else bmssp_insert_updates xs p0)
  end;

val bmssp_block_size : nat = one_nat;

val bmssp_infinity : nat =
  nat_of_num
    (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit1
  (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 (Bit0
(Bit1 (Bit0 (Bit1 (Bit1 (Bit1 One)))))))))))))))))));

val bmssp_bound : real = of_nat semiring_1_real bmssp_infinity;

fun bmssp_loop Zero_nat g vertices settled ds p = bmssp_normalize_dist ds
  | bmssp_loop (Suc fuel) g vertices settled ds p =
    let
      val (s, (_, p1)) = bp_pull equal_nat bmssp_block_size bmssp_bound p;
      val pulled =
        filter
          (fn x =>
            member equal_nat x s andalso not (membera equal_nat settled x))
          vertices;
    in
      (if null pulled then bmssp_normalize_dist ds
        else let
               val settleda = pulled @ settled;
               val relaxed = bmssp_relax_vertices g settleda pulled ds;
               val updates = fst relaxed;
               val dsa = snd relaxed;
               val a = bmssp_apply_updates updates p1;
             in
               bmssp_loop fuel g vertices settleda dsa a
             end)
    end;

val example_graph : (nat * (nat * nat)) list =
  [(Zero_nat, (one_nat, nat_of_num (Bit1 One))),
    (Zero_nat, (nat_of_num (Bit0 (Bit0 One)), nat_of_num (Bit0 (Bit1 One)))),
    (Zero_nat, (nat_of_num (Bit0 One), nat_of_num (Bit0 (Bit1 (Bit0 One))))),
    (one_nat, (nat_of_num (Bit0 One), nat_of_num (Bit0 One))),
    (one_nat, (nat_of_num (Bit0 (Bit0 One)), nat_of_num (Bit0 (Bit0 One)))),
    (one_nat, (nat_of_num (Bit1 One), nat_of_num (Bit1 (Bit0 (Bit0 One))))),
    (nat_of_num (Bit0 One), (nat_of_num (Bit1 One), nat_of_num (Bit1 One))),
    (nat_of_num (Bit0 One), (nat_of_num (Bit0 (Bit0 One)), one_nat)),
    (nat_of_num (Bit0 (Bit0 One)),
      (nat_of_num (Bit1 One), nat_of_num (Bit1 (Bit0 One))))];

fun bmssp_edge_vertices (u, (v, w)) = [u, v];

fun bmssp_vertices g s =
  sort_key linorder_nat (fn x => x)
    (remdups equal_nat (s :: maps bmssp_edge_vertices g));

fun bp_empty m b = Bucketed_partition_ext (m, b, [], (fn _ => b), ());

fun bmssp_distances g s =
  let
    val vertices = bmssp_vertices g s;
    val p0 = bp_empty bmssp_block_size bmssp_bound;
    val p1 =
      bp_result_of
        (c_bp_regularized_local_insert equal_nat s
          (bmssp_partition_key s Zero_nat) p0);
    val fuel = Suc (times_nat (size_list vertices) (Suc (size_list g)));
  in
    bmssp_loop fuel g vertices [] [(s, Zero_nat)] p1
  end;

val example_expected_dist : (nat * nat) list =
  [(Zero_nat, Zero_nat), (one_nat, nat_of_num (Bit1 One)),
    (nat_of_num (Bit0 One), nat_of_num (Bit1 (Bit0 One))),
    (nat_of_num (Bit1 One), nat_of_num (Bit0 (Bit0 (Bit0 One)))),
    (nat_of_num (Bit0 (Bit0 One)), nat_of_num (Bit0 (Bit1 One)))];

end; (*struct BMSSP*)
