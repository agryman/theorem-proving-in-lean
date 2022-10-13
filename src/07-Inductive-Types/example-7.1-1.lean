-- Enumerated Types

inductive weekday : Type
| sunday : weekday
| monday : weekday
| tuesday : weekday
| wednesday : weekday
| thursday : weekday
| friday : weekday
| saturday : weekday

#check weekday
#print weekday

#check weekday.sunday
#check weekday.monday

open weekday

#check sunday
#check monday

#check weekday.rec
#check @weekday.rec

#check weekday.rec_on
#check @weekday.rec_on

def number_of_day (d : weekday) : ℕ :=
weekday.rec_on d 1 2 3 4 5 6 7

#reduce number_of_day sunday
#reduce number_of_day monday
#reduce number_of_day tuesday

def number_of_day' (d : weekday) : ℕ :=
weekday.cases_on d 1 2 3 4 5 6 7

#reduce number_of_day' wednesday

namespace weekday
@[reducible]
private def cases_on := @weekday.cases_on

def number_of_day₁ (d : weekday) : nat :=
cases_on d 1 2 3 4 5 6 7
end weekday

#reduce weekday.number_of_day₁ weekday.sunday

open weekday (renaming cases_on → cases_on)

#reduce number_of_day₁ sunday
#check cases_on

namespace weekday
def next (d : weekday) : weekday :=
weekday.cases_on d monday tuesday wednesday thursday friday saturday sunday

def previous (d : weekday) : weekday :=
weekday.cases_on d saturday sunday monday tuesday wednesday thursday friday

#reduce next (next tuesday)
#reduce next (previous tuesday)

example : next (previous tuesday) = tuesday := rfl

theorem next_previous (d: weekday) : next (previous d) = d :=
weekday.cases_on d
  (show next (previous sunday) = sunday, from rfl)
  (show next (previous monday) = monday, from rfl)
  (show next (previous tuesday) = tuesday, from rfl)
  (show next (previous wednesday) = wednesday, from rfl)
  (show next (previous thursday) = thursday, from rfl)
  (show next (previous friday) = friday, from rfl)
  (show next (previous saturday) = saturday, from rfl)

theorem next_previous' (d: weekday) : next (previous d) = d :=
weekday.cases_on d rfl rfl rfl rfl rfl rfl rfl

theorem next_previous'' (d: weekday) : next (previous d) = d :=
by apply weekday.cases_on d; refl

theorem next_previous₁ (d: weekday) : next (previous d) = d :=
by apply weekday.rec_on d; refl

end weekday