// == define needed types ==

abstract sig Bool {}

one sig TRUE extends Bool {}

one sig FALSE extends Bool {}

abstract sig VehicleStatus {}

one sig ONGOING extends VehicleStatus {}

one sig CHARGING extends VehicleStatus {}

abstract sig SlotStatus {}

one sig FREE extends SlotStatus {}

one sig OCCUPIED extends SlotStatus {}

abstract sig SlotType {}

one sig SLOW extends SlotType {}

one sig FAST extends SlotType {}

one sig RAPID extends SlotType {}

// Signatures and relationships

sig User {
	email: one String,
	owns: one Vehicle
}

sig Vehicle {
	licensePlate: one String,
	vehicleStatus: one VehicleStatus
}

sig Dso {
	provideEnergyTo: set Cpo
}

sig Cpo {
	manages: some ChargingStation,
	getsEnergyFrom: some Dso
}

sig ChargingStation {
	batteryAvailable: one Bool,
	contains: some ChargingSlot,
	appliedOffers: set Offer
}

sig ChargingSlot {
	type: one SlotType,
	slotStatus: one SlotStatus,
	bookings: set Booking
}

sig Booking {
	user: one User,
	startTime: one Int,
	endTime: one Int,
	bookedSlot: one ChargingSlot
	// slotStatus: one SlotStatus
} {startTime > 0
   endTime > 0
   startTime < endTime}

sig Offer {
	startDate: one Int,
	endDate: one Int,
	discountPercentage: one Int
} {startDate > 0 
   endDate > 0
   endDate > startDate
   discountPercentage > 0}

// === FACTS ===

/**
 * If a station doesn't have batteries, it must
 * be connected to a DSO
 */
fact {
	all cpo: Cpo |
		all c: ChargingStation |
			c in cpo.manages implies 
				c.batteryAvailable in FALSE implies
					one d : Dso |
						d in cpo.getsEnergyFrom
}

/**
 * If a CPO gets energy from a DSO, then that very same DSO
 * must deliver energy to it
 */
fact {
	all cpo: Cpo |
		all d: Dso |
			d in cpo.getsEnergyFrom
			iff 
			cpo in d.provideEnergyTo
}

/**
 * Every charging station is managed by a unique CPO
 */
fact {
	all cs: ChargingStation | one cpo: Cpo | cs in cpo.manages
}

/**
 * Every charging slot is connected to a station
 */
fact {
	all s: ChargingSlot |
		one cs: ChargingStation |
			s in cs.contains
}

/**
 * The same special offer can't be applied by more than 1 station
 */
/*fact {
	all disj cs1, cs2: ChargingStation |
		cs1.appliedOffers & cs2.appliedOffers = none
}*/

/**
 * Each special offer must be associated with a station
 */
fact {
	all o: Offer |
		one cs: ChargingStation |
			o in cs.appliedOffers
}

/**
 * Validity periods of special offers can't overlap
 */
fact {
	all cs: ChargingStation |
		all disj o1, o2: Offer |
			(o1 in cs.appliedOffers and o2 in cs.appliedOffers)
			implies
			not overlaps[o1.startDate, o1.endDate, o2.startDate, o2.endDate]
}

/**
 * Each booking must be associated to a slot
 */
fact {
	all b: Booking |
		one s: ChargingSlot |
			b in s.bookings
}

/**
 *	Symmetry between slot and booking
 */
fact {
	all s: ChargingSlot |
		all b: Booking |
			b in s.bookings iff s = b.bookedSlot
}

/**
 * Bookings in the same slots don't overlap
 */
fact {
	/*all s: ChargingSlot |
		all b1: Booking |
			s = b1.bookedSlot
			implies
			no b2: Booking |
				s = b1.bookedSlot implies overlaps[b1.startTime, b1.endTime, b2.startTime, b2.endTime]*/
	all s: ChargingSlot |
		all disj b1, b2: Booking |
			(b1 in s.bookings and b2 in s.bookings)
			implies
			not overlaps[b1.startTime, b1.endTime, b2.startTime,b2.endTime]
}

/**
 * EndTime of a booking should respect performance of charging slots
 * (e.g. the endtime for fast charging must be earlier than one for a 
 * slow charge)
 */
fact {
	all cs: ChargingStation |
		all disj b1, b2: Booking |
			(b1.bookedSlot in cs.contains and b2.bookedSlot in cs.contains)
			implies
			complyToSlotSpeed[b1, b2] or complyToSlotSpeed[b2, b1]
}

/**
 * Every user has a different email
 */
fact noDuplicateEmail {
	no disj u1, u2: User | 
		u1.email = u2.email
}

/**
 * Each vehicle must be owned by a user
 */
fact {
	all v: Vehicle |
		one u: User |
			v in u.owns
}

// the following facts make sure that everything is connected

fact allSlotStatusConnected {
	all ss: SlotStatus |
		some s: ChargingSlot |
			s.slotStatus = ss
}

fact allSlotTypesConnected {
	all st: SlotType |
		some s: ChargingSlot |
			s.type = st
}

fact allVehicleStatusConnected {
	all vs: VehicleStatus |
		some v: Vehicle |
			v.vehicleStatus = vs
}

/**
 * Specify which are the strings that should be used in the world
 */
fact makeStringsResolve {
	none != "a" + "b" + "c" + "d"
}

// === ASSERTIONS ===

assert distinctCpoForEveryStation {
	all disj cpo1, cpo2: Cpo | cpo1.manages & cpo2.manages = none
}

//check distinctCpoForEveryStation

assert everyChargingStationDifferentSlots {
	no disj cs1, cs2: ChargingStation |
		cs1.contains & cs2.contains != none
}

// check everyChargingStationDifferentSlots

assert everySlotConnectedToStation {
	all s: ChargingSlot |
		one cs: ChargingStation |
			s in cs.contains
}

// check everySlotConnectedToStation

assert everyOfferIsUniqueToStation {
	no disj cs1, cs2: ChargingStation |
		cs1.appliedOffers & cs2.appliedOffers != none
}

// check everyOfferIsUniqueToStation

assert eachBookingHasStation {
	no b: Booking |
		no s: ChargingSlot |
			b in s.bookings
}

// check eachBookingHasStation

assert offersDontOverlap {
		all cs: ChargingStation |
			all disj o1, o2: Offer |
				(o1 in cs.appliedOffers and o2 in cs.appliedOffers)
				implies
				not overlaps[o1.startDate, o1.endDate, o2.startDate, o2.endDate]
}

// check offersDontOverlap

assert everyOfferHasStation {
	all o: Offer | one cs: ChargingStation | o in cs.appliedOffers
}

// check everyOfferHasStation

assert bookingsDontOverlap {
	all s: ChargingSlot |
		no disj b1, b2: Booking |
			(b1 in s.bookings and b2 in s.bookings)
			implies 
			overlaps[b1.startTime, b1.endTime, b2.startTime, b2.endTime]
}

// check bookingsDontOverlap

assert everyVehicleIsOwned {
	no v: Vehicle |
		all u: User |
			v not in u.owns
}

// check everyVehicleIsOwned

assert noUserWithoutBooking {
	all u: User |
		some b: Booking |
			u = b.user
}

// check noUserWithoutBooking

// === PREDICATES ===

pred overlaps[start1: Int, end1: Int, start2: Int, end2: Int] {
	(start1 = start2) or
	(start1 < start2 and start2 <= end1) or 
	(start1 > start2 and start1 <= end2)
}

/**
 * Sets the rules according to which
 * a booking for a faster slot must finish earlier than for a slower one
 */
pred complyToSlotSpeed[b1: Booking, b2: Booking] {
	b1.endTime < b2.endTime
	iff
	(b1.bookedSlot.type = RAPID and (b2.bookedSlot.type = FAST or b2.bookedSlot.type = SLOW)) or
	(b1.bookedSlot.type = FAST and b2.bookedSlot.type = SLOW)
}

// === WORLDS ===

pred world1 {
	#Cpo > 1
	#ChargingStation > 1
	#ChargingSlot > 3
	#Offer > #ChargingStation
	#Vehicle > 1
	#Booking > 2
	// #User > 0
	
	all u: User | all v: Vehicle | u.email != v.licensePlate
	some cs: ChargingStation | #cs.contains > 1
	some c: Cpo | #c.manages > 1
	some cs: ChargingStation | cs.batteryAvailable = FALSE
	some s: ChargingSlot | #s.bookings > 1
	some disj dso1, dso2: Dso | #dso1.provideEnergyTo > 1 and #dso2.provideEnergyTo > 1
}

run world1 for 10
