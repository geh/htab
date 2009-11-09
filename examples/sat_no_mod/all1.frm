% Input file in the format of hylolib 1.3

signature
{

propositions { tall, strong, pretty, naive }
nominals     { alice, bob, jean, marie, unknown }
relations    { love,
               lovedBy : {inverseof love},
               canManipulate : {trclosureof lovedBy},
               know : {reflexive},
               touches : {symmetric},
               U : {universal},
               fatherOf,
               motherOf,
               parentOf : {equals {fatherOf,motherOf}},
               childOf : {inverseof parentOf},
               youngerThan : {transitive, subsetof childOf}
             }

}

theory {
 [U]((tall & strong) --> pretty);

 alice: ( strong  & !tall & !naive);
 bob: ( tall & !strong ) ;

 (alice:bob) v jean:<love>marie;

 bob:[lovedBy]naive;

 alice:<youngerThan>marie;
 marie:<youngerThan>bob;
 bob:<youngerThan>jean;

 unknown:<parentOf>alice

}

query (satisfiable? , "out1") {
 alice:<canManipulate>jean
}

query (satisfiable? , "out2") {
 unknown:<parentOf>jean
}

query (retrieve , "retrieve1") {
 <youngerThan>jean
}

