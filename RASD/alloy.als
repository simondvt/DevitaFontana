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

abstract sig User {} // user can be Municipality or Normal User
sig Municipality extends User {
	zones:	   some Zone	, // zones that are in the territory of the Municipality
	solutions: set Solution
}

sig NormalUser extends User { 
	email:			one Email,
	segnalations: set Segnalation // set = 0 o più
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
fact segnalationsInSolutionSameZone {
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

/// ~facts ///

/// worlds ///
pred show {

}
run show 

/// ~worlds ///
