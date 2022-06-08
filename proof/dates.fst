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
  : Tot date
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
