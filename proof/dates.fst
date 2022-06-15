module Dates
open FStar.Mul

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

let days_in_month (month:int) (is_leap_year : bool) : option int =
  match month with
  | 1 | 3 | 5 | 7 | 8 | 10 | 12 -> Some 31
  | 4 | 6 | 9 | 11 -> Some 30
  | 2 -> if is_leap_year then Some 29 else Some 28
  | _ -> None

let is_valid_date (d : date) : bool =
  match days_in_month d.month (is_leap_year d.year) with
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

(** Returns new [year, month]. Precondition: [1 <= month <= 12] *)
let rec add_months_to_first_of_month_date
    (year : int)
    (month : int{1 <= month /\ month <= 12})
    (months : int)
    : Pure (int & int)
           (requires True)
           (ensures (fun (y, m) -> 1 <= m /\ m <= 12))
           (* The absolute value of the new_month always decreases, except
              maybe in the case where the next iteration will be terminal *)
           (decreases %[in_same_year month months; abs (month + months)]) =
  let new_month = month + months in
  if 1 <= new_month && new_month <= 12 then year, new_month
  else if new_month > 12 then (
    add_months_to_first_of_month_date (year + 1) month (months - 12)
  ) else
    (* new_month <= 0 *)
    add_months_to_first_of_month_date (year - 1) month (months + 12)

(* TODO: add_dates_year and add_dates_month require a proper handling of
   rounding *)

(* Some measure to express that being in the right year after adding the months
   period is a terminal case for the recursion below *)
let in_same_month (d:date{is_valid_date d}) (days:int) : GTot nat =
  let days_in_d_month = Some?.v (days_in_month d.month (is_leap_year d.year)) in
  let new_day = d.day + days in
  if 1 <= new_day && new_day <= days_in_d_month then 0
  else 1

let rec add_dates_days (d:date{is_valid_date d}) (days:int)
  : Tot (d:date{is_valid_date d})
        (decreases %[in_same_month d days; abs (d.day + days)]) =
  let days_in_d_month = Some?.v (days_in_month d.month (is_leap_year d.year)) in
  let new_day = d.day + days in
  if 1 <= new_day && new_day <= days_in_d_month then
    { d with day = new_day }
  else if new_day >= days_in_d_month then (
    let new_year, new_month =
      add_months_to_first_of_month_date d.year d.month 1
    in
    add_dates_days
      ({year = new_year; month = new_month; day = 1})
      (days - (days_in_d_month - d.day) - 1)
  ) else (
    let new_year, new_month =
      add_months_to_first_of_month_date d.year d.month (-1)
    in
    let new_day = Some?.v (days_in_month new_month (is_leap_year new_year)) in
    add_dates_days
      ({ year = new_year; month = new_month; day = new_day})
      (days + d.day)
  )

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
      let new_d2_year, new_d2_month =
        add_months_to_first_of_month_date d2.year d2.month 1
      in
      let new_d2 = {year = new_d2_year; month = new_d2_month; day = 1} in
      add_periods
        (make_period 0 0 (Some?.v (days_in_month d2.month (is_leap_year d2.year)) - d2.day + 1))
        (sub_dates d1 new_d2)
    end
  end


(*** Lemmas ***)

/// compare_dates returns 0 iff the two dates are equal
let lemma_compare_dates_refl (d1 d2:date) : Lemma
  (compare_dates d1 d2 = 0 <==> d1 = d2)
  = ()

/// (d + x1) + x2 == d + (x1 + x2)
val lemma_add_dates_assoc (d:date{is_valid_date d}) (x1 x2:int)
  : Lemma (ensures
    add_dates_days (add_dates_days d x1) x2 == add_dates_days d (x1 + x2))
    (decreases abs x1)

#push-options "--z3rlimit 50 --fuel 2 --ifuel 0"

let rec lemma_add_dates_assoc d x1 x2 =
  let days_in_d_month = Some?.v (days_in_month d.month (is_leap_year d.year)) in
  let new_day = d.day + x1 in
  if 1 <= new_day && new_day <= days_in_d_month then
    ()
  else
    if new_day >= days_in_d_month then (
      let new_year, new_month =
        add_months_to_first_of_month_date d.year d.month 1
      in
      let x1' = x1 - (days_in_d_month - d.day) - 1 in
      let d' = ({year = new_year; month = new_month; day = 1}) in
      lemma_add_dates_assoc d' x1' x2

    ) else (
      let new_year, new_month =
        add_months_to_first_of_month_date d.year d.month (-1)
      in
      let new_day = Some?.v (days_in_month new_month (is_leap_year new_year)) in
      let d' = ({ year = new_year; month = new_month; day = new_day}) in
      let x1' = x1 + d.day in
      lemma_add_dates_assoc d' x1' x2
    )

#pop-options

val lemma_add_neg_cancellative (d:date{is_valid_date d}) (x:int)
  : Lemma
  (ensures compare_dates (add_dates_days (add_dates_days d x) (-x) ) d == 0)
  (decreases abs x)

#push-options "--z3rlimit 50 --fuel 2 --ifuel 0"

let rec lemma_add_neg_cancellative d x =
  let days_in_d_month = Some?.v (days_in_month d.month (is_leap_year d.year)) in
  let new_day = d.day + x in
  if 1 <= new_day && new_day <= days_in_d_month then ()
  else (
    if new_day >= days_in_d_month then (
      let new_year, new_month =
        add_months_to_first_of_month_date d.year d.month 1
      in
      let x' = x - (days_in_d_month - d.day) - 1 in
      let d' = ({year = new_year; month = new_month; day = 1}) in
      lemma_add_neg_cancellative d' x';
      lemma_add_dates_assoc (add_dates_days d x) (-x') (x'-x)

    ) else (
      let new_year, new_month =
        add_months_to_first_of_month_date d.year d.month (-1)
      in
      let new_day = Some?.v (days_in_month new_month (is_leap_year new_year)) in
      let d' = ({ year = new_year; month = new_month; day = new_day}) in
      let x' = x + d.day in
      lemma_add_neg_cancellative d' x';
      lemma_add_dates_assoc (add_dates_days d x) (-x') (x'-x)
    )
  )

#pop-options
