signature
{ propositions { p }
  nominals { }
  relations { r ,
              i : {inverseof   r},
              t : {trclosureof r}
            }
}

 theory
{

p & <t>(!p & ([i]!p) & ([i][i]!p))

}
