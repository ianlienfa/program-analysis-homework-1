import python

// This predicate checks that a local variable is a parameter of a function.
predicate function_has_parameter(Function f, LocalVariable v) {
  v.isParameter() and v.getScope() = f
}

// Your code here
// --------------------

// Write a predicate that checks that a variable is a parameter of a function
// and has a default value of None. (15 points)
predicate parameter_default_none(Function f, LocalVariable v) {
  function_has_parameter(f, v) and
  exists(Parameter p, None n |
    p = f.getArgByName(v.getId()) and
    p.getDefault() = n
  )
}

// Write a predicate that checks if a function contains a statement of the form
// `v = v or ...` and return it.
// (see the "Predicates with result" section of the reference)
//
// This predicate must:
// - Check that v is a parameter of f (5 points).
// - Identify a statement inside the function that assigns v a value (10 points).
// - Check that the value is an Or expression (15 points).
// - Check that the first operand of the Or expression is the variable itself
//   (15 points).
// - Return the statement (10 points).
Stmt assigned_self_or_default(Function f, LocalVariable v) {
  function_has_parameter(f, v) and
  exists(Stmt stmt, AssignStmt assign, BoolExpr bool | 
    // Check assignment statement in function
    f.contains(stmt) and stmt.(AssignStmt) = assign 
    and 
    // Check if v is the one got assigned
    exists(Name assignee |  
      assign.getATarget() = assignee and assignee.getId() = v.getId()
    )
    and
    // Check or expression
    assign.getValue() = bool and bool.getOp() instanceof Or
    and
    // Check if the first operand is the variable ifself
    bool.getValue(0).toString() = v.getId()
    // Return result
    and result = stmt
  )  
}

// --------------------

from Function f, LocalVariable v, Stmt s
where
  parameter_default_none(f, v) and
  s = assigned_self_or_default(f, v)
select s, v