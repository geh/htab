signature {

propositions { p }
nominals     { n}
relations { r : {functional},
            s : {inverseof r} }

}

theory
{

E (p & <s><s>n) & E (!p & <s><s>n)

}
