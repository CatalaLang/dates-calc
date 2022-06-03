(* This file is part of the Dates_calc library. Copyright (C) 2022 Inria,
   contributors: Denis Merigoux <denis.merigoux@inria.fr>, Aymeric Fromherz
   <aymeric.fromherz@inria.fr>, Raphaël Monat <raphael.monat@lip6.fr>

   Licensed under the Apache License, Version 2.0 (the "License"); you may not
   use this file except in compliance with the License. You may obtain a copy of
   the License at

   http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
   WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
   License for the specific language governing permissions and limitations under
   the License. *)

[@@@warning "-27"]

type date = { year : int; month : int; day : int }
(** A valid date in the standard Gregorian calendar. *)

type period = { years : int; months : int; days : int }
(** A period can be any number and combination of days, months, years. *)

exception InvalidDate
exception AmbiguousComputation

type date_rounding =
  | RoundUp
  | RoundDown
  | AbortOnRound
      (** When choosing [AbortOnRound], functions may raise
          [AmbiguousComputation]. *)

(** {2 Functions on dates}*)

let is_leap_year ~(year : int) : bool =
  year mod 400 = 0 || (year mod 4 = 0 && year mod 100 <> 0)

(** @raise [InvalidDate]*)
let days_in_month ~(month : int) ~(is_leap_year : bool) : int =
  match month with
  | 1 | 3 | 5 | 7 | 8 | 10 | 12 -> 31
  | 4 | 6 | 9 | 11 -> 30
  | 2 -> if is_leap_year then 29 else 28
  | _ -> raise InvalidDate

let is_valid_date ~(year : int) ~(month : int) ~(day : int) : bool =
  try day >= 1 && day <= days_in_month ~month ~is_leap_year:(is_leap_year ~year)
  with InvalidDate -> false

(** @raise [InvalidDate]*)
let make_date ~(year : int) ~(month : int) ~(day : int) : date =
  if is_valid_date ~year ~month ~day then { year; month; day }
  else raise InvalidDate

(** @raise [AmbiguousComputation] *)
let add_dates ?(round : date_rounding = AbortOnRound) (d1 : date) (d2 : period)
    : date =
  failwith "Unimplemented!"

(** The returned [period] is always expressed as a number of days. *)
let sub_dates (d1 : date) (d2 : date) : period = failwith "Unimplemented!"

let compare_dates (d1 : date) (d2 : date) : int =
  if Int.compare d1.year d2.year = 0 then
    if Int.compare d1.month d2.month = 0 then Int.compare d1.day d2.day
    else Int.compare d1.month d2.month
  else Int.compare d1.year d2.year

let date_to_ymd (d : date) : int * int * int = d.year, d.month, d.day

(** Respects ISO8601 format. *)
let format_date (fmt : Format.formatter) (d : date) : unit =
  Format.fprintf fmt "%04d-%02d-%02d" d.year d.month d.day

(** {2 Functions on periods}*)

let make_period ~(years : int) ~(months : int) ~(days : int) : period =
  failwith "Unimplemented!"

let add_periods (d1 : period) (d2 : period) : period = failwith "Unimplemented!"
let sub_periods (d1 : period) (d2 : period) : period = failwith "Unimplemented!"
let mul_period (d1 : period) (m : int) : period = failwith "Unimplemented!"

(** @raise [AmbiguousComputation]
      when the period is anything else than a number of days. *)
let period_to_days (p : period) : int = failwith "Unimplemented!"
