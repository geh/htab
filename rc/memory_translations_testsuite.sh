# testsuite ensuring that translations from memory logic to all six
# relation-changing modal logics are correct

# part 1

# unsatisfiable memory logic formulas should be found unsatisfiable

# a. known is initially false

# known
# <> known
# <><> known
# <><><> known

# b. gadgets are independent

# p & (remember)!p
# <> true & (remember)[]false
# [] false & (remember)<>true


# part 2

# I. satisfiable memory logic formulas should be found satisfiable
# II. found models should be of expected shape
#     -> removing all s-states and t-states from the model should
#        yield a model for the input memory logic formula
