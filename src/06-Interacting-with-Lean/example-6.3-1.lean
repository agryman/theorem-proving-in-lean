-- 6.3. More on Namespaces

namespace foo
def bar : ℕ := 1
end foo

#check foo.bar

open foo
#check bar
