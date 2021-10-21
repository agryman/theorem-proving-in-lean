import algebra.ordered_ring

#check add_sub_cancel
#check nat.add_sub_cancel
#check _root_.add_sub_cancel

namespace foo
protected def bar : ℕ := 1
end foo

-- #check bar
#check foo.bar
