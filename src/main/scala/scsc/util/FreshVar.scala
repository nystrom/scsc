package scsc.util

import org.bitbucket.inkytonik.kiama.util.Counter

/**
 * Fresh variable name generator. To keep things simple, we generate
 * names of the form `_vn` where `n` is a unique number. These names
 * are guaranteed not to occur in user programs, so we do not have
 * to check for clashes.
 */
object FreshVar extends Counter {
  def apply(): String = s"_v${next()}"
}
