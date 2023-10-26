package notation

type Proof = [Z] =>> List[Z]

def Proof[Z](zs: Z*): List[Z] = List(zs: _*)
