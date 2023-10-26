package notation

type Proposition[Z] = Tuple2[Z, Z]

def Proposition[Z]: Tuple2[Z, Z] => Proposition[Z] = identity

