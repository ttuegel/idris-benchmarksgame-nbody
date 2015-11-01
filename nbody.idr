import Data.Vect

record Planet where
  constructor MkPlanet
  x, y, z : Double
  vx, vy, vz : Double
  mass : Double

initial : Vect 5 Planet
initial = sol :: jovian
  where
    solarMass : Double
    solarMass = 4 * pow pi 2
    daysPerYear : Double
    daysPerYear = 365.24
    jupiter : Planet
    jupiter = MkPlanet
                {- x =    -} (4.84143144246472090e+00)
                {- y =    -} (-1.16032004402742839e+00)
                {- z =    -} (-1.03622044471123109e-01)
                {- vx =   -} (1.66007664274403694e-03 * daysPerYear)
                {- vy =   -} (7.69901118419740425e-03 * daysPerYear)
                {- vz =   -} (-6.90460016972063023e-05 * daysPerYear)
                {- mass = -} (9.54791938424326609e-04 * solarMass)
    saturn : Planet
    saturn = MkPlanet
               {- x =    -} (8.34336671824457987e+00)
               {- y =    -} (4.12479856412430479e+00)
               {- z =    -} (-4.03523417114321381e-01)
               {- vx =   -} (-2.76742510726862411e-03 * daysPerYear)
               {- vy =   -} (4.99852801234917238e-03 * daysPerYear)
               {- vz =   -} (2.30417297573763929e-05 * daysPerYear)
               {- mass = -} (2.85885980666130812e-04 * solarMass)
    uranus : Planet
    uranus = MkPlanet
               {- x =    -} (1.28943695621391310e+01)
               {- y =    -} (-1.51111514016986312e+01)
               {- z =    -} (-2.23307578892655734e-01)
               {- vx =   -} (2.96460137564761618e-03 * daysPerYear)
               {- vy =   -} (2.37847173959480950e-03 * daysPerYear)
               {- vz =   -} (-2.96589568540237556e-05 * daysPerYear)
               {- mass = -} (4.36624404335156298e-05 * solarMass)
    neptune : Planet
    neptune = MkPlanet
                {- x =    -} (1.53796971148509165e+01)
                {- y =    -} (-2.59193146099879641e+01)
                {- z =    -} (1.79258772950371181e-01)
                {- vx =   -} (2.68067772490389322e-03 * daysPerYear)
                {- vy =   -} (1.62824170038242295e-03 * daysPerYear)
                {- vz =   -} (-9.51592254519715870e-05 * daysPerYear)
                {- mass = -} (5.15138902046611451e-05 * solarMass)
    jovian : Vect 4 Planet
    jovian = jupiter :: saturn :: uranus :: neptune :: Nil
    px : Double
    px = sum (map (\p => vx p * mass p) jovian)
    py : Double
    py = sum (map (\p => vy p * mass p) jovian)
    pz : Double
    pz = sum (map (\p => vz p * mass p) jovian)
    sol : Planet
    sol = MkPlanet
            {- x =    -} (0.0)
            {- y =    -} (0.0)
            {- z =    -} (0.0)
            {- vx =   -} (-px / solarMass)
            {- vy =   -} (-py / solarMass)
            {- vz =   -} (-pz / solarMass)
            {- mass = -} (solarMass)

kinetic1 : Planet -> Double
kinetic1 p = 0.5 * mass p * (pow (vx p) 2 + pow (vy p) 2 + pow (vz p) 2)

kinetic : Vect n Planet -> Double
kinetic planets = sum (map kinetic1 planets)

potential2 : Planet -> Planet -> Double
potential2 p q
  = let dx = x p - x q
        dy = y p - y q
        dz = z p - z q
        r = sqrt (pow dx 2 + pow dy 2 + pow dz 2)
    in - (mass p * mass q / r)

potential : Vect n Planet -> Double
potential = potential_go 0 where
  potential_go : Double -> Vect n Planet -> Double
  potential_go U Nil = U
  potential_go U (p :: ps) = potential_go (U + sum (map (potential2 p) ps)) ps

energy : Vect n Planet -> Double
energy planets = kinetic planets + potential planets

dt : Double
dt = 0.01

accelerate1 : Planet -> Vect n Planet -> (Planet, Vect n Planet)
accelerate1 p Nil = (p, Nil)
accelerate1 p ps = accelerate1_go p (reverse ps) Nil where

  plusReducesS : (j : Nat) -> (k : Nat) -> plus j (S k) = S (plus j k)
  plusReducesS Z k = Refl
  plusReducesS (S i) k = cong (plusReducesS i k)

  accelerate1_go : Planet -> Vect i Planet -> Vect j Planet -> (Planet, Vect (j + i) Planet)
  accelerate1_go this Nil result ?= (this, result)
  accelerate1_go this (next :: rest) result ?=
    let dx = x this - x next
        dy = y this - y next
        dz = z this - z next
        rr = pow dx 2 + pow dy 2 + pow dz 2
        ff = dt / (rr * sqrt rr)
        fThis = mass next * ff
        this' = record { vx = vx this - dx * fThis
                       , vy = vy this - dy * fThis
                       , vz = vz this - dz * fThis
                       } this
        fNext = mass this * ff
        next' = record { vx = vx next + dx * fNext
                       , vy = vy next + dy * fNext
                       , vz = vz next + dz * fNext
                       } next
    in accelerate1_go this' rest (next' :: result)

accelerate : Vect n Planet -> Vect n Planet
accelerate Nil = Nil
accelerate (p :: ps)
  = let (q, qs) = accelerate1 p ps
    in q :: accelerate qs

move1 : Planet -> Planet
move1 p
  = record { x = x p + dt * vx p
           , y = y p + dt * vy p
           , z = z p + dt * vz p
           } p

move : Vect n Planet -> Vect n Planet
move = map move1

advance : Vect n Planet -> Vect n Planet
advance = move . accelerate

main : IO ()
main = do
  putStrLn (show (energy initial))

---------- Proofs ----------

Main.accelerate1_go_lemma_2 = proof
  intros
  rewrite plusSuccRightSucc j k
  trivial


Main.accelerate1_go_lemma_1 = proof
  intros
  rewrite plusCommutative 0 j
  trivial


