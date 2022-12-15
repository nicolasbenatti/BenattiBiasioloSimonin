// == define needed types ==

abstract sig Bool {}

sig True extends Bool {}

sig False extends Bool {}

// Signatures and relationships

sig Planning {}

sig Offer {}

sig User {
	carLicensePlate: one String,
	email: one String,
	organize: one Planning,
}

sig Vehicle {
	ownedBy: one User
}

sig Dso {
	provideEnergyTo: set Cpo
}

sig Cpo {
	manages: some ChargingStation,
	getsEnergyFrom: one Dso
}

sig ChargingStation {
	batteryAvailable: one Bool,
	contains: some ChargingSlot,
	appliedOffers: set Offer
}

sig ChargingSlot {
	organizedBy: one Planning
}

// === facts ===
/*fact noDuplicateData {
	no disj u1, u2: User | 
		u1.carLicensePlate = u2.carLicensePlate or
		u1.email = u2.email
}*/

/*
 * each charging slot must be connected to a station
 */
/*fact allSlotsHaveStation {
	all cs: ChargingSlot |
		one cst: ChargingStation | cs in cst.contains
}*/

/*
 * each station is managed by exactly 1 CPO 
 */
/*fact allStationsOneCpo {
	all cpo1, cpo2: Cpo |
		cpo1.manages & cpo2.manages = none
}*/

pred world1 {
	#ChargingStation > 1
}

run world1 for 2
