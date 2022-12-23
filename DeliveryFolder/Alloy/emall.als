// == Types and Constants ==

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

// === Signatures and Relationships ===

sig User {
	email: one String,
	owns: one Vehicle,
	isChargingTo: one ChargingSlot
}

sig Vehicle {
	licensePlate: one String,
	vehicleStatus: one VehicleStatus
}

sig Dso {
	energyPrice: one Int,
	provideEnergyTo: set Cpo
} {energyPrice > 0}

sig Cpo {
	storeThreshold: one Int,
	manages: some ChargingStation,
	getsEnergyFrom: some Dso,
	storesEnergyFrom: lone Dso
} {storeThreshold > 0}

sig ChargingStation {
	batteryAvailable: one Bool,
	contains: some ChargingSlot,
	appliedOffers: set Offer,
}

sig ChargingSlot {
	type: one SlotType,
	slotStatus: one SlotStatus,
	bookings: set Booking
}

sig Booking {
	performedBy: one User,
	startTime: one Int,
	endTime: one Int,
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

// === Facts ===

/**
 * If a station doesn't have batteries, it must
 * be connected to a DSO
 */
fact {
	all cpo: Cpo |
		all c: ChargingStation |
			c in cpo.manages
			implies 
			(c.batteryAvailable = FALSE 
			implies
			one d : Dso |
				d in cpo.getsEnergyFrom)
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
 * A CPO can store energy only if at least one of the station it manages
 * has got batteries available
 */
fact {
	all cpo: Cpo |
		cpo.storesEnergyFrom != none
		implies
		(some cs: ChargingStation |
		cs in cpo.manages
		implies
		cs.batteryAvailable = TRUE)
}

/**
 * If a CPO stores energy from a certain DSO,
 * its price must be lower than the computed threshold
 */
fact {
	all cpo: Cpo |
		all dso: Dso |
			dso = cpo.storesEnergyFrom
			implies
			dso.energyPrice < cpo.storeThreshold
}

/**
 * Every charging station is managed by a unique CPO
 */
fact {
	all cs: ChargingStation |
		one cpo: Cpo |
			cs in cpo.manages
}

/**
 * If the user is charging to a slot, then the slot must be taken
 */
fact {
	all u: User |
		all s: ChargingSlot |
			s = u.isChargingTo
			implies
			s.slotStatus = OCCUPIED
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
 * Each special offer must be associated with a station
 */
fact {
	all o: Offer |
		one cs: ChargingStation |
			o in cs.appliedOffers
}

/**
 * Validity periods of special offers don't overlap
 */
fact {
	all cs: ChargingStation |
		all disj o1, o2: Offer |
			(o1 in cs.appliedOffers and o2 in cs.appliedOffers)
			implies
			not overlaps[o1.startDate, o1.endDate, o2.startDate, o2.endDate]
}

/**
 * Every booking must be associated to a slot
 */
fact {
	all b: Booking |
		one s: ChargingSlot |
			b in s.bookings
}

/**
 * Bookings in the same slots don't overlap
 */
fact {
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
		all disj s1, s2: ChargingSlot |
			(s1 in cs.contains and s2 in cs.contains)
			implies
			all disj b1, b2: Booking |
				(b1 in (s1.bookings + s2.bookings) and
				 b2 in (s1.bookings + s2.bookings))
				implies
				complyToSlotSpeed[cs, s1, s2, b1, b2]
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

/**
 * user email and vehicle's license plate must be
 * different strings
 */
fact {
	all u: User |
		all v: Vehicle |
			u.email != v.licensePlate
}

/**
 * Each vehicle must have a different license plate
 */
fact {
	all disj v1, v2: Vehicle |
		v1.licensePlate != v2.licensePlate
}

// The following facts make sure that every constant is connected

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

// === Assertions ===



// === Predicates ===

pred overlaps[start1, end1, start2, end2: Int] {
	(start1 = start2) or
	(start1 < start2 and start2 <= end1) or 
	(start1 > start2 and start1 <= end2)
}

/**
 * Sets the rules according to which
 * a booking for a faster slot must finish earlier than for a slower one
 */
pred complyToSlotSpeed[cs: ChargingStation, s1, s2: ChargingSlot, b1, b2: Booking] {
	((s1.type = RAPID and s2.type = FAST)
	implies
	b1.endTime < b2.endTime)
	or
	((s1.type = RAPID and s2.type = SLOW)
	implies
	b1.endTime < b2.endTime)
	or
	((s1.type = FAST and s2.type = SLOW)
	implies
	b1.endTime < b2.endTime)
}

// === Dynamic modeling ===

pred addBooking[b: Booking, u: User, s, s': ChargingSlot, start, end: Int] {
	b.performedBy = u
	b.startTime = start
	b.endTime = end
	s'.bookings = s.bookings + b
}

run addBooking

pred addOffer[cs, cs': ChargingStation, o: Offer, s, e, p: Int] {
	o.startDate = s
	o.endDate = e
	o.discountPercentage = p
	cs'.appliedOffers = cs.appliedOffers + o
}

run addOffer

// === Worlds ===

pred completeWorld {
	#Cpo > 1
	#ChargingStation > 1
	#ChargingSlot > #ChargingStation
	#Offer > #ChargingStation
	#Vehicle > 1
	#Booking > #ChargingStation	

	some cs: ChargingStation | #cs.contains > 1
	some c: Cpo | #c.manages > 1
	some cs: ChargingStation | cs.batteryAvailable = FALSE
	some s: ChargingSlot | #s.bookings > 1
	some disj dso1, dso2: Dso | #dso1.provideEnergyTo > 1 and #dso2.provideEnergyTo > 1
}

run completeWorld for 5
