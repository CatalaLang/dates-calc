module Dates

(* Needed for using the standard * as multiplication operator *)
open FStar.Mul

(** Basic types *)

type date = {
  year : int;
  month : int;
  day : int
}

type period = {
  years : int;
  months : int;
  days : int
}

(** Functions on periods **)

let make_period (years : int) (months : int) (days : int) : period =
  { years; months; days }

let add_periods (d1 d2:period) : period =
  { years = d1.years + d2.years;
    months = d1.months + d2.months;
    days = d1.days + d2.days
  }

let sub_periods (d1 d2:period) : period =
  { years = d1.years - d2.years;
    months = d1.months - d2.months;
    days = d1.days - d2.days
  }

let mul_period (d:period) (m : int) : period =
  { years = d.years * m; months = d.months * m; days = d.days * m }

(* To remain in F*'s Pure realm to simplify proofs,
   we will use options instead of exceptions *)
let period_to_days (p : period) : option int =
  if p.years <> 0 || p.months <> 0 then None else Some p.days

(** Functions on dates **)

let is_leap_year (year : int) : bool =
  year % 400 = 0 || (year % 4 = 0 && year % 100 <> 0)

let nb_days (month:int) (year : int) : option int =
  match month with
  | 1 | 3 | 5 | 7 | 8 | 10 | 12 -> Some 31
  | 4 | 6 | 9 | 11 -> Some 30
  | 2 -> if is_leap_year year then Some 29 else Some 28
  | _ -> None

let is_valid_date (d : date) : bool =
  match nb_days d.month d.year with
  | None -> false
  | Some days -> d.day >= 1 && d.day <= days

let make_date (year month day: int) : option date =
  let d = {year; month; day} in
  if is_valid_date d then Some d else None

(* Some measure to express that being in the right year after adding the months
   period is a terminal case for the recursion below *)
let in_same_year (month months:int) : GTot nat =
  if 1 <= month + months && month + months <= 12 then 0
  else 1

let add_dates_years (d: date) (years: int) : date = {d with year = d.year + years}

(** Returns new [year, month] *)
let rec add_dates_months
    (d:date)
    (months : int)
    : Pure date
           (requires True)
           (ensures fun d -> 1 <= d.month /\ d.month <= 12)
           (* The absolute value of the new_month always decreases, except
              maybe in the case where the next iteration will be terminal *)
           (decreases %[in_same_year d.month months; abs (d.month + months)]) =
  let new_month = d.month + months in
  // Add-Month case
  if 1 <= new_month && new_month <= 12 then {d with month = new_month}
  else if new_month > 12 then (
    // Add-Month-Over case
    add_dates_months {d with year = d.year + 1} (months - 12)
  ) else
    // Add-Month-Under case
    (* new_month <= 0 *)
    add_dates_months {d with year = d.year - 1} (months + 12)

(* Some measure to express that being in the right year after adding the months
   period is a terminal case for the recursion below *)
let in_same_month (d:date{is_valid_date d}) (days:int) : GTot nat =
  let days_in_d_month = Some?.v (nb_days d.month d.year) in
  let new_day = d.day + days in
  if 1 <= new_day && new_day <= days_in_d_month then 0
  else 1

(* Day addition function when the date is valid *)
let rec add_dates_days_valid (d:date{is_valid_date d}) (days:int)
  : Tot (d:date{is_valid_date d})
        (decreases %[in_same_month d days; abs (d.day + days); abs (d.day)]) =
  let days_in_d_month = Some?.v (nb_days d.month d.year) in
  let new_day = d.day + days in
  if 1 <= new_day && new_day <= days_in_d_month then
    // Add-Days case
    { d with day = new_day }
  else if new_day >= days_in_d_month then (
    // Add-Days-Over case
    let d' = add_dates_months d 1
    in
    add_dates_days_valid
      {d' with day = 1}
      (days - (days_in_d_month - d.day) - 1)
  ) else (
    if 1 < d.day && new_day <= 0 then
      // Add-Days-Under1 case
      add_dates_days_valid {d with day = 1} (new_day - 1)
    else (
      // Confirming that the Add-Days-Under2 pattern requiring day to be 1 applies
      assert (d.day = 1);
      // Add-Days-Under2 case
      // Computing m', d' in hypothesis
      let d' = add_dates_months d (-1)
      in
      add_dates_days_valid
        {d' with day = 1}
        (days + Some?.v (nb_days d'.month d'.year))
    )
  )

(* Day addition function. None corresponds to the error (or "bottom") case.
   The case returning None encapsulates Add-Days-Err1 and Add-Days-Err2.
*)
let add_dates_days (d:date) (days: int) : Tot (option date) =
  if d.day < 1 || None? (nb_days d.month d.year) || d.day > Some?.v (nb_days d.month d.year) then None
  else Some (add_dates_days_valid d days)

let compare_dates (d1 d2:date) : int =
  if d1.year - d2.year = 0 then
    if d1.month - d2.month = 0 then d1.day - d2.day
    else d1.month - d2.month
  else d1.year - d2.year

let neg_period (p:period) : period =
  { years = -p.years; months = -p.months; days = -p.days }

type period_days = p:period{p.years = 0 /\ p.months = 0}

(* A termination measure used below, which decreases when d1 > d2 instead of d1 < d2 *)
let dates_compare_sign (d1 d2:date)
  = if d1.year = d2.year && d1.month = d2.month then 0
    else if compare_dates d1 d2 < 0 then 2
    else 1

(** The returned period is always expressed as a number of days *)
let rec sub_dates (d1:date{is_valid_date d1}) (d2:date{is_valid_date d2})
  : Tot period_days
  (decreases %[dates_compare_sign d1 d2; abs (d1.year - d2.year); 12 - d2.month]) =
  if d1.year = d2.year && d1.month = d2.month then
    make_period 0 0 (d1.day - d2.day)
  else begin
    let cmp = compare_dates d1 d2 in
    if cmp < 0 then
      neg_period (sub_dates d2 d1)
    else begin
      let d2' = add_dates_months d2 1 in
      let new_d2 = {d2' with day = 1} in
      add_periods
        (make_period 0 0 (Some?.v (nb_days d2.month d2.year) - d2.day + 1))
        (sub_dates d1 new_d2)
    end
  end

(* Rounding down operator *)
let round_down (d:date) : option (d:date{is_valid_date d}) =
  let nb = nb_days d.month d.year in
  // Round-Err1 case, and implicit failure is nb_days is not defined
  if None? nb || d.day < 1 then None
  // Round-Down case
  else if d.day > Some?.v nb then Some {d with day = Some?.v nb}
  // Round-noop case
  else Some d


(* Rounding down operator *)
let round_up (d:date) : option (d:date{is_valid_date d}) =
  let nb = nb_days d.month d.year in
  // Round-Err1 case, and implicit failure is nb_days is not defined
  if None? nb || d.day < 1 then None
  // Round-Up case
  else if d.day > Some?.v nb then
    let d' = add_dates_months d 1 in
    Some {d' with day = 1}
  // Round-noop case
  else Some d

let round_err (d:date) : option (d:date{is_valid_date d}) =
  let nb = nb_days d.month d.year in
  // Round-Err1 case, and implicit failure is nb_days is not defined
  if None? nb || d.day < 1 then None
  // Round-Down case
  else if d.day > Some?.v nb then None
  // Round-noop case
  else Some d

(* Derived semantics: Definition of the three derived forms *)

let add_up (d:date) (p:period) : option date =
   match round_up (add_dates_months (add_dates_years d p.years) p.months) with
   | None -> None
   | Some d -> add_dates_days d p.days

let add_down (d:date) (p:period) : option date =
   match round_down (add_dates_months (add_dates_years d p.years) p.months) with
   | None -> None
   | Some d -> add_dates_days d p.days

let add_err (d:date) (p:period) : option date =
   match round_err (add_dates_months (add_dates_years d p.years) p.months) with
   | None -> None
   | Some d -> add_dates_days d p.days

(*** Lemmas ***)

/// compare_dates returns 0 iff the two dates are equal
let lemma_compare_dates_refl (d1 d2:date) : Lemma
  (compare_dates d1 d2 = 0 <==> d1 = d2)
  = ()

/// (d + x1) + x2 == d + (x1 + x2)
val lemma_add_dates_assoc (d:date{is_valid_date d}) (x1 x2:int)
  : Lemma (ensures
    add_dates_days_valid (add_dates_days_valid d x1) x2 == add_dates_days_valid d (x1 + x2))
    (decreases abs x1)

#push-options "--z3rlimit 50 --fuel 2 --ifuel 0"

let rec lemma_add_dates_assoc d x1 x2 =
  admit();
  let days_in_d_month = Some?.v (nb_days d.month d.year) in
  let new_day = d.day + x1 in
  if 1 <= new_day && new_day <= days_in_d_month then
    ()
  else
    if new_day >= days_in_d_month then (
      let new_year, new_month =
        add_dates_months d.year d.month 1
      in
      let x1' = x1 - (days_in_d_month - d.day) - 1 in
      let d' = ({year = new_year; month = new_month; day = 1}) in
      lemma_add_dates_assoc d' x1' x2

    ) else (
      let new_year, new_month =
        add_dates_months d.year d.month (-1)
      in
      let new_day = Some?.v (nb_days new_month new_year) in
      let d' = ({ year = new_year; month = new_month; day = new_day}) in
      let x1' = x1 + d.day in
      lemma_add_dates_assoc d' x1' x2
    )

#pop-options

val lemma_add_neg_cancellative (d:date{is_valid_date d}) (x:int)
  : Lemma
  (ensures add_dates_days_valid (add_dates_days_valid d x) (-x) == d)
  (decreases abs x)

#push-options "--z3rlimit 50 --fuel 2 --ifuel 0"

let rec lemma_add_neg_cancellative d x =
  admit();
  let days_in_d_month = Some?.v (nb_days d.month d.year) in
  let new_day = d.day + x in
  if 1 <= new_day && new_day <= days_in_d_month then ()
  else (
    if new_day >= days_in_d_month then (
      let new_year, new_month =
        add_dates_months d.year d.month 1
      in
      let x' = x - (days_in_d_month - d.day) - 1 in
      let d' = ({year = new_year; month = new_month; day = 1}) in
      lemma_add_neg_cancellative d' x';
      lemma_add_dates_assoc (add_dates_days_valid d x) (-x') (x'-x)

    ) else (
      let new_year, new_month =
        add_dates_months d.year d.month (-1)
      in
      let new_day = Some?.v (nb_days new_month new_year) in
      let d' = ({ year = new_year; month = new_month; day = new_day}) in
      let x' = x + d.day in
      lemma_add_neg_cancellative d' x';
      lemma_add_dates_assoc (add_dates_days_valid d x) (-x') (x'-x)
    )
  )

#pop-options

val lemma_equal_dates_implies_zero_sub
   (d1:date{is_valid_date d1})
   (d2:date{is_valid_date d2})
   : Lemma (requires compare_dates d1 d2 = 0)
           (ensures (sub_dates d1 d2).days = 0)

let lemma_equal_dates_implies_zero_sub d1 d2 = ()

val lemma_greater_date_implies_positive_sub
   (d1:date{is_valid_date d1})
   (d2:date{is_valid_date d2})
   : Lemma (requires compare_dates d1 d2 > 0)
           (ensures (sub_dates d1 d2).days > 0)
           (decreases
             %[abs (d1.year - d2.year); 12 - d2.month])

let rec lemma_greater_date_implies_positive_sub d1 d2 =
  if d1.year = d2.year && d1.month = d2.month then ()
  else
    let new_d2_year, new_d2_month =
      add_dates_months d2.year d2.month 1
    in
    let new_d2 = {year = new_d2_year; month = new_d2_month; day = 1} in
    assert (d1.year - d2.year > 0 \/ (d1.year - d2.year = 0 /\ d1.month - d2.month > 0));
    if compare_dates d1 new_d2 = 0 then ()
    else lemma_greater_date_implies_positive_sub d1 new_d2

val lemma_smaller_date_implies_negative_sub
   (d1:date{is_valid_date d1})
   (d2:date{is_valid_date d2})
   : Lemma (requires compare_dates d1 d2 < 0)
           (ensures (sub_dates d1 d2).days < 0)

let lemma_smaller_date_implies_negative_sub d1 d2 =
  if d1.year = d2.year && d1.month = d2.month then ()
  else lemma_greater_date_implies_positive_sub d2 d1

/// forall d1 d2, compare_dates (add_dates d2 (sub_dates d1 d2)) d1 = 0.
/// Since sub_dates always return a period_days, we state this using add_dates_days
val lemma_add_sub_cancellative
   (d1:date{is_valid_date d1})
   (d2:date{is_valid_date d2})
   : Lemma
     (ensures add_dates_days_valid d2 ((sub_dates d1 d2).days) == d1)
     (decreases %[dates_compare_sign d1 d2; abs (d1.year - d2.year); 12 - d2.month])

#push-options "--z3rlimit 20"

let rec lemma_add_sub_cancellative d1 d2 =
  admit();
  if d1.year = d2.year && d1.month = d2.month then ()
  else begin
    let cmp = compare_dates d1 d2 in
    if cmp >= 0 then (
      lemma_greater_date_implies_positive_sub d1 d2;
      let new_d2_year, new_d2_month =
        add_dates_months d2.year d2.month 1
      in
      let new_d2 = {year = new_d2_year; month = new_d2_month; day = 1} in
      lemma_add_sub_cancellative d1 new_d2

    ) else (
      lemma_add_sub_cancellative d2 d1;
      (**) assert (add_dates_days_valid d1 ((sub_dates d2 d1).days) == d2);
      lemma_add_neg_cancellative d1 ((sub_dates d2 d1).days);
      (**) assert (d1 == add_dates_days_valid d2 (- (sub_dates d2 d1).days));
      (**) assert ((sub_dates d1 d2).days == - (sub_dates d2 d1).days)
    )
  end

#pop-options



(* Properties to prove:

Theorem 1: Strong normalization. Got it since we are using an interpreter

Lemma 1: If the date is valid, adding n days returns a non-empty date -> Ok by definitional interpreter

Lemma 2: Adding a day/month to a valid date does not return bottom and returns day >= 1 (but can return invalid date)

Lemma 3: If the date is not bottom, rounding returns a valid date

Theorem 2: Addition of a period to a valid date with rounding returns a valid date

Theorem 3: Monotonicity, If d1 < d2, adding a period with rounding returns d1 + p <= d2 + p

Lemma 4: for all d, n, d +_y n = d +_m (12 * n(

Lemma 5: Monotonicity of year and month addition

Lemma 6: Monotonicity of day addition, requires valid dates

Lemma 7: Monotonicity of rounding

Theorem 4.1 : Montonicity of rounding down/up

Theorem 4.2 Both rounding modes equivalent if non-ambiguous computation

Theorem 5: Characterization of ambiguous month addition
