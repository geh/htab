signature {
propositions { p }
nominals { }
relations { student,
            course,
            tag : { equals {student, course}} }
}

theory

{
 <tag>p;
 [student]!p;
 [course]!p
}
