/// signatures ///

sig Email { // NormalUser's email
} {some user: NormalUser | user.email = this }

sig TypeOfViolation { // Segnalation's typeOfViolation
} {(some segnalation: Segnalation | segnalation.typeOfViolation = this) or 
	 (some solution: Solution | solution.typeOfViolation = this)}

sig Location { // a location is identified via latitude and langitude
	latitude:		one Int,
	longitude: one Int
} 

sig Zone { // a zone is identified via the set of its locations
	locations: some Location
}

sig Segnalation { // a location is composed of a location and its type
	location:			one Location,
	typeOfViolation: one TypeOfViolation
}

sig Solution { // a solution includes a set of segnalations that occurred in a zone
	segnalations: some Segnalation,
	zone:		one Zone,
	typeOfViolation: one TypeOfViolation
}

abstract sig User { // user can be Municipality or Normal User
	statisticalData: set StatisticalData
} 

sig Municipality extends User {
	zones:	   some Zone	, // zones that are in the territory of the Municipality
	solutions: set Solution
}

sig NormalUser extends User { 
	email:			one Email,
	segnalations: set Segnalation // set = 0 o più
}

sig Permission {} {some sd: StatisticalData | sd.permission = this}

one sig DB { // database storing the permissions each user has
	usersPermissions: User -> Permission
}

sig StatisticalData { // users can access this statistical data with the given permission
	permission: one Permission
}

/// ~signatures ///


/// facts ///

// normal users sign up with different emails
fact usersWithDifferentEmail {
	no disj u1, u2: NormalUser | u1.email = u2.email
}

// each segnalation is associated to a single normal user
fact segnalationAssociatedToUniqueUser {
	all segnalation: Segnalation | one user: NormalUser | segnalation in user.segnalations
}

// each segnalation occur in a zone
fact segnalationOccurredInZone {
	all segnalation: Segnalation | some zone: Zone | segnalation.location in zone.locations
}

// each solution is associated to a single municipality
fact solutionAssociatedToUniqueMunicipality {
	all solution: Solution | one municipality: Municipality | solution in municipality.solutions
}

// all segnalations that triggered a solution occurred in the same zone
fact segnalationsInSolutionSameZone {
	all solution:Solution | all segnalation: solution.segnalations
		| some zoneLocation: solution.zone.locations | segnalation.location in zoneLocation
}

// all segnalations that triggered a solution concern the same type of violation
fact segnalationsInSolutionConcernSameTypeOfViolation {
	all solution:Solution | all segnalation: solution.segnalations
		| some tov: TypeOfViolation | segnalation.typeOfViolation = tov and solution.typeOfViolation = tov
}

// the solutions that municipality receives occur in a zone which is in the municipality
fact solutionConcerningMunicipalityZones {
	all municipality: Municipality | all solution: municipality.solutions
		| solution.zone in municipality.zones
}

// each municipality has different zones
fact differentMunicipalityZones {
	no disj m1, m2: Municipality | m1.zones & m2.zones != none
}

// each location belongs to only one Zone
fact locationBelongsToOneZone {
	all location: Location | one  zone: Zone | location in zone.locations
}

// each zone belongs to a municipality
fact zoneBelongsToMunicipality {
	all zone: Zone | some municipality: Municipality | zone in municipality.zones
}

// each segnalation belongs to 0 or 1 solution
fact segnalationBelongsToMax1Solution {
	all segnalation: Segnalation | lone solution: Solution | segnalation in solution.segnalations
}

// each segnalation is associated to a NormalUser
fact segnalationAssociatedToNormalUser {
	all segnalation: Segnalation | one user: NormalUser | segnalation in user.segnalations
}

// a user has access to statistical data for which he has the permission
fact UserAccessStatisticalData {
	all u: User | all sd: StatisticalData | (sd.permission in u.(DB.usersPermissions))
				 implies sd in u.statisticalData
}

/// ~facts ///

/// predicates ///

pred addNormalUserIntoDB [db, db': DB, u: NormalUser, p: Permission] {
	db'.usersPermissions = db.usersPermissions + u -> p
}

pred addMunicipalityIntoDB [db, db': DB, m: Municipality] {
	all p: Permission | db'.usersPermissions = db.usersPermissions + m -> p
}

/// ~predicates ///

/// assertions ///

assert SolutionToOneMunicipality { // a solution must be sent to only one municipality
	no disj m1, m2: Municipality | some s: Solution | s in m1.solutions and s in m2.solutions
}

assert MunicipalityAccessAllStatisticalData { // municipality has access to all statistical data
	all m: Municipality, db, db': DB | addMunicipalityIntoDB [db, db', m] 
			implies all sd: StatisticalData | sd.permission in m.(DB.usersPermissions)
}

check SolutionToOneMunicipality
check MunicipalityAccessAllStatisticalData

/// ~assertions ///

/// worlds ///
pred world1 {
	(#Municipality = 1) and
	(#NormalUser = 3) and (all u: NormalUser | u.segnalations != none) and
	(#Zone > 2)
}

pred world2 {
	(#Municipality = 2) and
	(#NormalUser >=  2)  and
	(all m: Municipality | m.solutions != none)
}

/// ~worlds ///
